#define _POSIX_C_SOURCE 200809L

#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <glob.h>
#include <limits.h>
#include <pwd.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <termios.h>
#include <unistd.h>

#ifdef USE_READLINE
#include <readline/history.h>
#include <readline/readline.h>
#endif

/*
 * One-file interactive shell for macOS/Linux terminals.
 * Supports: quoting, $VAR expansion, ; && || | & (subshell),
 * redirections < > >> 2> 2>>, and jobs/fg/bg.
 */

typedef enum {
    TOK_WORD = 1,
    TOK_PIPE,
    TOK_AND_IF,
    TOK_OR_IF,
    TOK_SEMI,
    TOK_AMP,
    TOK_LPAREN,
    TOK_RPAREN,
    TOK_REDIR,
    TOK_EOF
} TokenType;

typedef enum {
    R_IN = 1,
    R_OUT,
    R_APPEND,
    R_HEREDOC,
    R_DUP,
    R_OUT_ERR,
    R_APPEND_ERR
} RedirType;

typedef struct {
    TokenType type;
    char *text;
    int quoted;
    int redir_fd;
    int redir_dup_fd;
    RedirType redir_type;
} Token;

typedef struct {
    Token *data;
    size_t len;
    size_t cap;
} TokenVec;

typedef struct Redir {
    int fd;
    RedirType type;
    char *target;
    int dup_fd;
    struct Redir *next;
} Redir;

typedef enum {
    NODE_CMD = 1,
    NODE_SUBSHELL,
    NODE_PIPE,
    NODE_AND,
    NODE_OR,
    NODE_SEQ,
    NODE_BG
} NodeType;

typedef struct Node Node;

struct Node {
    NodeType type;
    union {
        struct {
            char **argv;
            int *quoted;
            int argc;
            int cap;
            Redir *redirs;
        } cmd;
        struct {
            Node *child;
            Redir *redirs;
        } subshell;
        struct {
            Node *left;
            Node *right;
        } bin;
        struct {
            Node *child;
        } unary;
    } as;
};

typedef struct {
    Token *toks;
    size_t ntok;
    size_t pos;
    char err[256];
} Parser;

typedef enum {
    PROC_RUNNING = 1,
    PROC_STOPPED,
    PROC_DONE
} ProcState;

typedef struct {
    pid_t pid;
    ProcState state;
    int raw_status;
} ProcEntry;

typedef struct Job {
    int id;
    pid_t pgid;
    char *cmdline;
    ProcEntry *procs;
    int nproc;
    pid_t last_pid;
    int last_raw_status;
    int notified;
    struct Job *next;
} Job;

typedef struct SavedFD {
    int fd;
    int saved;
    struct SavedFD *next;
} SavedFD;

static int g_last_status = 0;
static pid_t g_last_bg = 0;
static int g_should_exit = 0;
static int g_exit_status = 0;

static int g_interactive = 0;
static int g_shell_terminal = STDIN_FILENO;
static pid_t g_shell_pgid = -1;
static struct termios g_shell_tmodes;

static Job *g_jobs = NULL;
static int g_next_job_id = 1;

typedef struct LocalVar {
    char *name;
    char *value;
    struct LocalVar *next;
} LocalVar;

typedef struct Alias {
    char *name;
    char *value;
    struct Alias *next;
} Alias;

static LocalVar *g_locals = NULL;
static Alias *g_aliases = NULL;
static char *g_shell_path = NULL;
static char *g_history_path = NULL;
#ifndef USE_READLINE
typedef struct {
    char **items;
    int len;
    int cap;
    int base;
    int max_entries;
} SimpleHistory;

static SimpleHistory g_simple_history = {NULL, 0, 0, 1, 5000};
#endif
static const char *const g_builtin_names[] = {
    "cd", "exit", "jobs", "fg", "bg", "export", "unset", "pwd", "echo", "history",
    "alias", "type", "which", "kill", "true", "false", NULL
};

static bool is_name_start(int c);
static bool is_name_char(int c);
static int command_assignment_prefix(char **argv, int argc);
static int is_builtin_name(const char *s);
static void shell_using_history(void);
static void shell_add_history(const char *line);
static int shell_read_history(const char *path);
static int shell_write_history(const char *path);
static void shell_stifle_history(int max_entries);
static int shell_history_base(void);
static int shell_history_length(void);
static const char *shell_history_get_line(int idx);
static char *shell_readline(const char *prompt);
static void shell_history_cleanup(void);

static void die(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fputc('\n', stderr);
    exit(1);
}

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) {
        die("out of memory");
    }
    return p;
}

static void *xrealloc(void *p, size_t n) {
    void *q = realloc(p, n ? n : 1);
    if (!q) {
        die("out of memory");
    }
    return q;
}

static char *xstrdup(const char *s) {
    char *p = strdup(s ? s : "");
    if (!p) {
        die("out of memory");
    }
    return p;
}

#ifndef USE_READLINE
static void simple_history_shrink_to_limit(void) {
    while (g_simple_history.max_entries > 0 && g_simple_history.len > g_simple_history.max_entries) {
        free(g_simple_history.items[0]);
        memmove(g_simple_history.items, g_simple_history.items + 1, sizeof(char *) * (size_t)(g_simple_history.len - 1));
        g_simple_history.len--;
        g_simple_history.base++;
    }
}
#endif

static void shell_using_history(void) {
#ifdef USE_READLINE
    using_history();
#endif
}

static void shell_add_history(const char *line) {
    if (!line || !*line) {
        return;
    }
#ifdef USE_READLINE
    add_history(line);
#else
    if (g_simple_history.len == g_simple_history.cap) {
        g_simple_history.cap = g_simple_history.cap ? g_simple_history.cap * 2 : 128;
        g_simple_history.items =
            xrealloc(g_simple_history.items, sizeof(char *) * (size_t)g_simple_history.cap);
    }
    g_simple_history.items[g_simple_history.len++] = xstrdup(line);
    simple_history_shrink_to_limit();
#endif
}

static int shell_read_history(const char *path) {
#ifdef USE_READLINE
    return read_history(path);
#else
    if (!path || !*path) {
        errno = EINVAL;
        return -1;
    }
    FILE *fp = fopen(path, "r");
    if (!fp) {
        if (errno == ENOENT) {
            return 0;
        }
        return -1;
    }
    char *line = NULL;
    size_t cap = 0;
    ssize_t n = 0;
    while ((n = getline(&line, &cap, fp)) >= 0) {
        while (n > 0 && (line[n - 1] == '\n' || line[n - 1] == '\r')) {
            line[--n] = '\0';
        }
        shell_add_history(line);
    }
    free(line);
    fclose(fp);
    return 0;
#endif
}

static int shell_write_history(const char *path) {
#ifdef USE_READLINE
    return write_history(path);
#else
    if (!path || !*path) {
        errno = EINVAL;
        return -1;
    }
    FILE *fp = fopen(path, "w");
    if (!fp) {
        return -1;
    }
    for (int i = 0; i < g_simple_history.len; i++) {
        if (fprintf(fp, "%s\n", g_simple_history.items[i]) < 0) {
            fclose(fp);
            return -1;
        }
    }
    fclose(fp);
    return 0;
#endif
}

static void shell_stifle_history(int max_entries) {
#ifdef USE_READLINE
    stifle_history(max_entries);
#else
    g_simple_history.max_entries = max_entries;
    simple_history_shrink_to_limit();
#endif
}

static int shell_history_base(void) {
#ifdef USE_READLINE
    return history_base;
#else
    return g_simple_history.base;
#endif
}

static int shell_history_length(void) {
#ifdef USE_READLINE
    return history_length;
#else
    return g_simple_history.len;
#endif
}

static const char *shell_history_get_line(int idx) {
#ifdef USE_READLINE
    HIST_ENTRY *e = history_get(idx);
    if (!e) {
        return NULL;
    }
    return e->line;
#else
    int off = idx - g_simple_history.base;
    if (off < 0 || off >= g_simple_history.len) {
        return NULL;
    }
    return g_simple_history.items[off];
#endif
}

static char *shell_readline(const char *prompt) {
#ifdef USE_READLINE
    return readline(prompt);
#else
    if (prompt) {
        fputs(prompt, stdout);
        fflush(stdout);
    }
    char *line = NULL;
    size_t cap = 0;
    ssize_t n = getline(&line, &cap, stdin);
    if (n < 0) {
        free(line);
        return NULL;
    }
    while (n > 0 && (line[n - 1] == '\n' || line[n - 1] == '\r')) {
        line[--n] = '\0';
    }
    return line;
#endif
}

static void shell_history_cleanup(void) {
#ifndef USE_READLINE
    for (int i = 0; i < g_simple_history.len; i++) {
        free(g_simple_history.items[i]);
    }
    free(g_simple_history.items);
    g_simple_history.items = NULL;
    g_simple_history.len = 0;
    g_simple_history.cap = 0;
#endif
}

static int valid_name(const char *s) {
    if (!s || !*s) {
        return 0;
    }
    if (!is_name_start((unsigned char)s[0])) {
        return 0;
    }
    for (size_t i = 1; s[i]; i++) {
        if (!is_name_char((unsigned char)s[i])) {
            return 0;
        }
    }
    return 1;
}

static LocalVar *local_find(const char *name) {
    for (LocalVar *v = g_locals; v; v = v->next) {
        if (strcmp(v->name, name) == 0) {
            return v;
        }
    }
    return NULL;
}

static const char *local_get(const char *name) {
    LocalVar *v = local_find(name);
    return v ? v->value : NULL;
}

static void local_set(const char *name, const char *value) {
    LocalVar *v = local_find(name);
    if (v) {
        free(v->value);
        v->value = xstrdup(value ? value : "");
        return;
    }
    v = xmalloc(sizeof(*v));
    v->name = xstrdup(name);
    v->value = xstrdup(value ? value : "");
    v->next = g_locals;
    g_locals = v;
}

static void local_unset(const char *name) {
    LocalVar *prev = NULL;
    LocalVar *cur = g_locals;
    while (cur) {
        if (strcmp(cur->name, name) == 0) {
            if (prev) {
                prev->next = cur->next;
            } else {
                g_locals = cur->next;
            }
            free(cur->name);
            free(cur->value);
            free(cur);
            return;
        }
        prev = cur;
        cur = cur->next;
    }
}

static void local_free_all(void) {
    LocalVar *cur = g_locals;
    while (cur) {
        LocalVar *next = cur->next;
        free(cur->name);
        free(cur->value);
        free(cur);
        cur = next;
    }
    g_locals = NULL;
}

static Alias *alias_find(const char *name) {
    for (Alias *a = g_aliases; a; a = a->next) {
        if (strcmp(a->name, name) == 0) {
            return a;
        }
    }
    return NULL;
}

static const char *alias_get(const char *name) {
    Alias *a = alias_find(name);
    return a ? a->value : NULL;
}

static void alias_set(const char *name, const char *value) {
    Alias *a = alias_find(name);
    if (a) {
        free(a->value);
        a->value = xstrdup(value ? value : "");
        return;
    }
    a = xmalloc(sizeof(*a));
    a->name = xstrdup(name);
    a->value = xstrdup(value ? value : "");
    a->next = g_aliases;
    g_aliases = a;
}

static void alias_free_all(void) {
    Alias *cur = g_aliases;
    while (cur) {
        Alias *next = cur->next;
        free(cur->name);
        free(cur->value);
        free(cur);
        cur = next;
    }
    g_aliases = NULL;
}

static const char *lookup_var(const char *name) {
    const char *v = local_get(name);
    if (v) {
        return v;
    }
    return getenv(name);
}

static void tv_push(TokenVec *tv, Token tk) {
    if (tv->len == tv->cap) {
        tv->cap = tv->cap ? tv->cap * 2 : 32;
        tv->data = xrealloc(tv->data, tv->cap * sizeof(Token));
    }
    tv->data[tv->len++] = tk;
}

static void tv_free(TokenVec *tv) {
    for (size_t i = 0; i < tv->len; i++) {
        free(tv->data[i].text);
    }
    free(tv->data);
    tv->data = NULL;
    tv->len = 0;
    tv->cap = 0;
}

typedef struct {
    char *buf;
    size_t len;
    size_t cap;
} StrBuf;

static void sb_init(StrBuf *sb) {
    sb->buf = NULL;
    sb->len = 0;
    sb->cap = 0;
}

static void sb_ensure(StrBuf *sb, size_t need) {
    if (sb->len + need + 1 <= sb->cap) {
        return;
    }
    size_t ncap = sb->cap ? sb->cap : 64;
    while (sb->len + need + 1 > ncap) {
        ncap *= 2;
    }
    sb->buf = xrealloc(sb->buf, ncap);
    sb->cap = ncap;
}

static void sb_addc(StrBuf *sb, char c) {
    sb_ensure(sb, 1);
    sb->buf[sb->len++] = c;
    sb->buf[sb->len] = '\0';
}

static void sb_adds(StrBuf *sb, const char *s) {
    size_t n = strlen(s);
    sb_ensure(sb, n);
    memcpy(sb->buf + sb->len, s, n);
    sb->len += n;
    sb->buf[sb->len] = '\0';
}

static char *sb_take(StrBuf *sb) {
    if (!sb->buf) {
        return xstrdup("");
    }
    char *p = sb->buf;
    sb->buf = NULL;
    sb->len = sb->cap = 0;
    return p;
}

static bool is_name_start(int c) {
    return isalpha((unsigned char)c) || c == '_';
}

static bool is_name_char(int c) {
    return isalnum((unsigned char)c) || c == '_';
}

static void sb_add_num(StrBuf *sb, long v) {
    char tmp[64];
    snprintf(tmp, sizeof(tmp), "%ld", v);
    sb_adds(sb, tmp);
}

static void expand_dollar(StrBuf *sb, const char *s, size_t *i) {
    /* s[*i] == '$' */
    size_t p = *i + 1;
    char c = s[p];

    if (c == '\0') {
        sb_addc(sb, '$');
        *i = p;
        return;
    }
    if (c == '?') {
        sb_add_num(sb, g_last_status);
        *i = p + 1;
        return;
    }
    if (c == '$') {
        sb_add_num(sb, (long)getpid());
        *i = p + 1;
        return;
    }
    if (c == '!') {
        sb_add_num(sb, (long)g_last_bg);
        *i = p + 1;
        return;
    }
    if (c == '{') {
        p++;
        size_t st = p;
        while (s[p] && s[p] != '}') {
            p++;
        }
        if (s[p] != '}') {
            sb_addc(sb, '$');
            *i = *i + 1;
            return;
        }
        size_t n = p - st;
        char *name = xmalloc(n + 1);
        memcpy(name, s + st, n);
        name[n] = '\0';
        const char *val = lookup_var(name);
        if (val) {
            sb_adds(sb, val);
        }
        free(name);
        *i = p + 1;
        return;
    }
    if (is_name_start((unsigned char)c)) {
        size_t st = p;
        p++;
        while (is_name_char((unsigned char)s[p])) {
            p++;
        }
        size_t n = p - st;
        char *name = xmalloc(n + 1);
        memcpy(name, s + st, n);
        name[n] = '\0';
        const char *val = lookup_var(name);
        if (val) {
            sb_adds(sb, val);
        }
        free(name);
        *i = p;
        return;
    }

    /* Unknown form -> literal '$' */
    sb_addc(sb, '$');
    *i = *i + 1;
}

static char *capture_subcommand_output(const char *cmd) {
    FILE *fp = popen(cmd, "r");
    if (!fp) {
        return xstrdup("");
    }

    StrBuf out;
    sb_init(&out);
    char buf[512];
    while (fgets(buf, sizeof(buf), fp)) {
        sb_adds(&out, buf);
    }
    pclose(fp);

    char *s = sb_take(&out);
    size_t n = strlen(s);
    while (n > 0 && (s[n - 1] == '\n' || s[n - 1] == '\r')) {
        n--;
    }
    for (size_t i = 0; i < n; i++) {
        if (s[i] == '\n' || s[i] == '\r') {
            s[i] = ' ';
        }
    }
    s[n] = '\0';
    return s;
}

static char *parse_dollar_subst(const char *line, size_t *i, char *err, size_t errsz) {
    /* line[*i] == '$' && line[*i + 1] == '(' */
    size_t p = *i + 2;
    size_t start = p;
    int depth = 1;
    while (line[p]) {
        if (line[p] == '\\' && line[p + 1]) {
            p += 2;
            continue;
        }
        if (line[p] == '\'') {
            p++;
            while (line[p] && line[p] != '\'') {
                p++;
            }
            if (!line[p]) {
                snprintf(err, errsz, "unterminated quote in $(...)");
                return NULL;
            }
            p++;
            continue;
        }
        if (line[p] == '"') {
            p++;
            while (line[p] && line[p] != '"') {
                if (line[p] == '\\' && line[p + 1]) {
                    p += 2;
                    continue;
                }
                p++;
            }
            if (!line[p]) {
                snprintf(err, errsz, "unterminated quote in $(...)");
                return NULL;
            }
            p++;
            continue;
        }
        if (line[p] == '$' && line[p + 1] == '(') {
            depth++;
            p += 2;
            continue;
        }
        if (line[p] == ')') {
            depth--;
            if (depth == 0) {
                size_t n = p - start;
                char *cmd = xmalloc(n + 1);
                memcpy(cmd, line + start, n);
                cmd[n] = '\0';
                *i = p + 1;
                return cmd;
            }
            p++;
            continue;
        }
        p++;
    }
    snprintf(err, errsz, "unterminated $(...)");
    return NULL;
}

static char *parse_backtick_subst(const char *line, size_t *i, char *err, size_t errsz) {
    /* line[*i] == '`' */
    size_t p = *i + 1;
    size_t start = p;
    while (line[p]) {
        if (line[p] == '\\' && line[p + 1]) {
            p += 2;
            continue;
        }
        if (line[p] == '`') {
            size_t n = p - start;
            char *cmd = xmalloc(n + 1);
            memcpy(cmd, line + start, n);
            cmd[n] = '\0';
            *i = p + 1;
            return cmd;
        }
        p++;
    }
    snprintf(err, errsz, "unterminated backtick command substitution");
    return NULL;
}

static bool is_op_char(char c) {
    return c == '|' || c == '&' || c == ';' || c == '(' || c == ')' || c == '<' || c == '>';
}

static int contains_glob_meta(const char *s) {
    for (size_t i = 0; s[i]; i++) {
        if (s[i] == '*' || s[i] == '?' || s[i] == '[') {
            return 1;
        }
    }
    return 0;
}

static int lex_word(const char *line, size_t *i, char **out, int *quoted, char *err, size_t errsz) {
    StrBuf sb;
    sb_init(&sb);
    int had_quote = 0;

    while (line[*i]) {
        char c = line[*i];
        if (isspace((unsigned char)c) || is_op_char(c)) {
            break;
        }

        if (c == '\\') {
            had_quote = 1;
            if (line[*i + 1]) {
                sb_addc(&sb, line[*i + 1]);
                *i += 2;
            } else {
                *i += 1;
            }
            continue;
        }

        if (c == '\'') {
            had_quote = 1;
            *i += 1;
            while (line[*i] && line[*i] != '\'') {
                sb_addc(&sb, line[*i]);
                *i += 1;
            }
            if (line[*i] != '\'') {
                snprintf(err, errsz, "unterminated single quote");
                free(sb.buf);
                return -1;
            }
            *i += 1;
            continue;
        }

        if (c == '"') {
            had_quote = 1;
            *i += 1;
            while (line[*i] && line[*i] != '"') {
                char d = line[*i];
                if (d == '\\' && line[*i + 1]) {
                    char n = line[*i + 1];
                    if (n == '\\' || n == '"' || n == '$' || n == '`') {
                        sb_addc(&sb, n);
                        *i += 2;
                        continue;
                    }
                }
                if (d == '$' && line[*i + 1] == '(') {
                    char *cmd = parse_dollar_subst(line, i, err, errsz);
                    if (!cmd) {
                        free(sb.buf);
                        return -1;
                    }
                    char *out = capture_subcommand_output(cmd);
                    sb_adds(&sb, out);
                    free(out);
                    free(cmd);
                    continue;
                }
                if (d == '`') {
                    char *cmd = parse_backtick_subst(line, i, err, errsz);
                    if (!cmd) {
                        free(sb.buf);
                        return -1;
                    }
                    char *out = capture_subcommand_output(cmd);
                    sb_adds(&sb, out);
                    free(out);
                    free(cmd);
                    continue;
                }
                if (d == '$') {
                    expand_dollar(&sb, line, i);
                    continue;
                }
                sb_addc(&sb, d);
                *i += 1;
            }
            if (line[*i] != '"') {
                snprintf(err, errsz, "unterminated double quote");
                free(sb.buf);
                return -1;
            }
            *i += 1;
            continue;
        }

        if (c == '$' && line[*i + 1] == '(') {
            char *cmd = parse_dollar_subst(line, i, err, errsz);
            if (!cmd) {
                free(sb.buf);
                return -1;
            }
            char *out = capture_subcommand_output(cmd);
            sb_adds(&sb, out);
            free(out);
            free(cmd);
            continue;
        }

        if (c == '`') {
            char *cmd = parse_backtick_subst(line, i, err, errsz);
            if (!cmd) {
                free(sb.buf);
                return -1;
            }
            char *out = capture_subcommand_output(cmd);
            sb_adds(&sb, out);
            free(out);
            free(cmd);
            continue;
        }

        if (c == '$') {
            expand_dollar(&sb, line, i);
            continue;
        }

        if (c == '~' && sb.len == 0) {
            const char *home = getenv("HOME");
            if (home) {
                sb_adds(&sb, home);
            } else {
                sb_addc(&sb, '~');
            }
            *i += 1;
            continue;
        }

        sb_addc(&sb, c);
        *i += 1;
    }

    *out = sb_take(&sb);
    *quoted = had_quote;
    return 0;
}

static int lex_line(const char *line, TokenVec *tv, char *err, size_t errsz) {
    size_t i = 0;

    while (line[i]) {
        while (isspace((unsigned char)line[i])) {
            i++;
        }
        if (!line[i]) {
            break;
        }
        if (line[i] == '#') {
            break;
        }

        Token tk;
        memset(&tk, 0, sizeof(tk));
        tk.redir_fd = -1;
        tk.redir_dup_fd = -1;

        if (line[i] == '&' && line[i + 1] == '&') {
            tk.type = TOK_AND_IF;
            i += 2;
            tv_push(tv, tk);
            continue;
        }
        if (line[i] == '|' && line[i + 1] == '|') {
            tk.type = TOK_OR_IF;
            i += 2;
            tv_push(tv, tk);
            continue;
        }

        if (isdigit((unsigned char)line[i])) {
            size_t j = i;
            while (isdigit((unsigned char)line[j])) {
                j++;
            }
            if (line[j] == '>' || line[j] == '<') {
                char num[32];
                size_t n = j - i;
                if (n >= sizeof(num)) {
                    snprintf(err, errsz, "redir fd too long");
                    return -1;
                }
                memcpy(num, line + i, n);
                num[n] = '\0';
                tk.type = TOK_REDIR;
                tk.redir_fd = atoi(num);
                if (line[j] == '<') {
                    if (line[j + 1] == '<') {
                        tk.redir_type = R_HEREDOC;
                        i = j + 2;
                    } else {
                        tk.redir_type = R_IN;
                        i = j + 1;
                    }
                } else {
                    if (line[j + 1] == '&') {
                        size_t k = j + 2;
                        if (!isdigit((unsigned char)line[k])) {
                            snprintf(err, errsz, "expected fd after >&");
                            return -1;
                        }
                        while (isdigit((unsigned char)line[k])) {
                            k++;
                        }
                        char fdnum[32];
                        size_t fdn = k - (j + 2);
                        if (fdn >= sizeof(fdnum)) {
                            snprintf(err, errsz, "dup fd too long");
                            return -1;
                        }
                        memcpy(fdnum, line + j + 2, fdn);
                        fdnum[fdn] = '\0';
                        tk.redir_type = R_DUP;
                        tk.redir_dup_fd = atoi(fdnum);
                        i = k;
                    } else if (line[j + 1] == '>') {
                        tk.redir_type = R_APPEND;
                        i = j + 2;
                    } else {
                        tk.redir_type = R_OUT;
                        i = j + 1;
                    }
                }
                tv_push(tv, tk);
                continue;
            }
        }

        if (line[i] == '&' && line[i + 1] == '>') {
            tk.type = TOK_REDIR;
            tk.redir_fd = -1;
            if (line[i + 2] == '>') {
                tk.redir_type = R_APPEND_ERR;
                i += 3;
            } else {
                tk.redir_type = R_OUT_ERR;
                i += 2;
            }
            tv_push(tv, tk);
            continue;
        }

        if (line[i] == '<' || line[i] == '>') {
            tk.type = TOK_REDIR;
            if (line[i] == '<') {
                if (line[i + 1] == '<') {
                    tk.redir_fd = 0;
                    tk.redir_type = R_HEREDOC;
                    i += 2;
                } else {
                    tk.redir_fd = 0;
                    tk.redir_type = R_IN;
                    i += 1;
                }
            } else {
                tk.redir_fd = 1;
                if (line[i + 1] == '&') {
                    size_t k = i + 2;
                    if (isdigit((unsigned char)line[k])) {
                        while (isdigit((unsigned char)line[k])) {
                            k++;
                        }
                        char fdnum[32];
                        size_t fdn = k - (i + 2);
                        if (fdn >= sizeof(fdnum)) {
                            snprintf(err, errsz, "dup fd too long");
                            return -1;
                        }
                        memcpy(fdnum, line + i + 2, fdn);
                        fdnum[fdn] = '\0';
                        tk.redir_type = R_DUP;
                        tk.redir_dup_fd = atoi(fdnum);
                        i = k;
                    } else {
                        tk.redir_type = R_OUT_ERR;
                        tk.redir_fd = -1;
                        i += 2;
                    }
                } else if (line[i + 1] == '>') {
                    tk.redir_type = R_APPEND;
                    i += 2;
                } else {
                    tk.redir_type = R_OUT;
                    i += 1;
                }
            }
            tv_push(tv, tk);
            continue;
        }

        if (line[i] == '|') {
            tk.type = TOK_PIPE;
            i += 1;
            tv_push(tv, tk);
            continue;
        }
        if (line[i] == '&') {
            tk.type = TOK_AMP;
            i += 1;
            tv_push(tv, tk);
            continue;
        }
        if (line[i] == ';') {
            tk.type = TOK_SEMI;
            i += 1;
            tv_push(tv, tk);
            continue;
        }
        if (line[i] == '(') {
            tk.type = TOK_LPAREN;
            i += 1;
            tv_push(tv, tk);
            continue;
        }
        if (line[i] == ')') {
            tk.type = TOK_RPAREN;
            i += 1;
            tv_push(tv, tk);
            continue;
        }

        tk.type = TOK_WORD;
        if (lex_word(line, &i, &tk.text, &tk.quoted, err, errsz) != 0) {
            return -1;
        }
        tv_push(tv, tk);
    }

    Token eof;
    memset(&eof, 0, sizeof(eof));
    eof.type = TOK_EOF;
    eof.redir_fd = -1;
    eof.redir_dup_fd = -1;
    tv_push(tv, eof);
    return 0;
}

static Node *node_new(NodeType t) {
    Node *n = xmalloc(sizeof(Node));
    memset(n, 0, sizeof(*n));
    n->type = t;
    return n;
}

static Node *node_bin(NodeType t, Node *l, Node *r) {
    Node *n = node_new(t);
    n->as.bin.left = l;
    n->as.bin.right = r;
    return n;
}

static Node *node_bg(Node *child) {
    Node *n = node_new(NODE_BG);
    n->as.unary.child = child;
    return n;
}

static void redir_append(Redir **head, Redir *r) {
    if (!*head) {
        *head = r;
        return;
    }
    Redir *cur = *head;
    while (cur->next) {
        cur = cur->next;
    }
    cur->next = r;
}

static void cmd_add_arg(Node *cmd, const char *word, int quoted) {
    if (cmd->as.cmd.argc == cmd->as.cmd.cap) {
        cmd->as.cmd.cap = cmd->as.cmd.cap ? cmd->as.cmd.cap * 2 : 8;
        cmd->as.cmd.argv = xrealloc(cmd->as.cmd.argv, sizeof(char *) * cmd->as.cmd.cap);
        cmd->as.cmd.quoted = xrealloc(cmd->as.cmd.quoted, sizeof(int) * cmd->as.cmd.cap);
    }
    cmd->as.cmd.argv[cmd->as.cmd.argc] = xstrdup(word);
    cmd->as.cmd.quoted[cmd->as.cmd.argc] = quoted;
    cmd->as.cmd.argc++;
}

static void free_redirs(Redir *r) {
    while (r) {
        Redir *n = r->next;
        free(r->target);
        free(r);
        r = n;
    }
}

static void free_node(Node *n) {
    if (!n) {
        return;
    }
    switch (n->type) {
        case NODE_CMD:
            for (int i = 0; i < n->as.cmd.argc; i++) {
                free(n->as.cmd.argv[i]);
            }
            free(n->as.cmd.argv);
            free(n->as.cmd.quoted);
            free_redirs(n->as.cmd.redirs);
            break;
        case NODE_SUBSHELL:
            free_node(n->as.subshell.child);
            free_redirs(n->as.subshell.redirs);
            break;
        case NODE_PIPE:
        case NODE_AND:
        case NODE_OR:
        case NODE_SEQ:
            free_node(n->as.bin.left);
            free_node(n->as.bin.right);
            break;
        case NODE_BG:
            free_node(n->as.unary.child);
            break;
    }
    free(n);
}

static Token *p_peek(Parser *p) {
    return &p->toks[p->pos];
}

static int p_match(Parser *p, TokenType t) {
    if (p_peek(p)->type == t) {
        p->pos++;
        return 1;
    }
    return 0;
}

static int p_expect(Parser *p, TokenType t, const char *msg) {
    if (p_match(p, t)) {
        return 1;
    }
    snprintf(p->err, sizeof(p->err), "%s", msg);
    return 0;
}

static int p_is_cmd_start(TokenType t) {
    return t == TOK_WORD || t == TOK_LPAREN || t == TOK_REDIR;
}

static void argv_add_glob(Node *cmd, const char *word, int quoted) {
    if (!quoted && contains_glob_meta(word)) {
        glob_t g;
        memset(&g, 0, sizeof(g));
        int rc = glob(word, GLOB_NOCHECK, NULL, &g);
        if (rc == 0) {
            for (size_t i = 0; i < g.gl_pathc; i++) {
                cmd_add_arg(cmd, g.gl_pathv[i], 1);
            }
            globfree(&g);
            return;
        }
        globfree(&g);
    }
    cmd_add_arg(cmd, word, quoted);
}

static Redir *parse_one_redir(Parser *p) {
    Token *op = p_peek(p);
    if (op->type != TOK_REDIR) {
        return NULL;
    }
    p->pos++;

    Redir *r = xmalloc(sizeof(Redir));
    r->fd = op->redir_fd;
    r->type = op->redir_type;
    r->target = NULL;
    r->dup_fd = op->redir_dup_fd;
    r->next = NULL;

    if (op->redir_type == R_DUP) {
        return r;
    }

    Token *arg = p_peek(p);
    if (arg->type != TOK_WORD) {
        snprintf(p->err, sizeof(p->err), "expected file name after redirection");
        free(r);
        return NULL;
    }
    p->pos++;
    r->target = xstrdup(arg->text ? arg->text : "");
    return r;
}

static Node *parse_list(Parser *p);

static Node *parse_command(Parser *p) {
    if (p_match(p, TOK_LPAREN)) {
        Node *inner = parse_list(p);
        if (!inner) {
            if (!p->err[0]) {
                snprintf(p->err, sizeof(p->err), "empty subshell");
            }
            return NULL;
        }
        if (!p_expect(p, TOK_RPAREN, "expected ')'")) {
            free_node(inner);
            return NULL;
        }

        Node *sub = node_new(NODE_SUBSHELL);
        sub->as.subshell.child = inner;

        while (p_peek(p)->type == TOK_REDIR) {
            Redir *r = parse_one_redir(p);
            if (!r) {
                free_node(sub);
                return NULL;
            }
            redir_append(&sub->as.subshell.redirs, r);
        }
        return sub;
    }

    Node *cmd = node_new(NODE_CMD);
    int saw_any = 0;

    while (1) {
        Token *t = p_peek(p);
        if (t->type == TOK_WORD) {
            saw_any = 1;
            argv_add_glob(cmd, t->text ? t->text : "", t->quoted);
            p->pos++;
            continue;
        }
        if (t->type == TOK_REDIR) {
            saw_any = 1;
            Redir *r = parse_one_redir(p);
            if (!r) {
                free_node(cmd);
                return NULL;
            }
            redir_append(&cmd->as.cmd.redirs, r);
            continue;
        }
        break;
    }

    if (!saw_any) {
        free_node(cmd);
        snprintf(p->err, sizeof(p->err), "expected command");
        return NULL;
    }
    return cmd;
}

static Node *parse_pipeline(Parser *p) {
    Node *left = parse_command(p);
    if (!left) {
        return NULL;
    }
    while (p_match(p, TOK_PIPE)) {
        Node *right = parse_command(p);
        if (!right) {
            free_node(left);
            if (!p->err[0]) {
                snprintf(p->err, sizeof(p->err), "expected command after '|'");
            }
            return NULL;
        }
        left = node_bin(NODE_PIPE, left, right);
    }
    return left;
}

static Node *parse_and_or(Parser *p) {
    Node *left = parse_pipeline(p);
    if (!left) {
        return NULL;
    }
    while (1) {
        if (p_match(p, TOK_AND_IF)) {
            Node *right = parse_pipeline(p);
            if (!right) {
                free_node(left);
                if (!p->err[0]) {
                    snprintf(p->err, sizeof(p->err), "expected command after &&");
                }
                return NULL;
            }
            left = node_bin(NODE_AND, left, right);
            continue;
        }
        if (p_match(p, TOK_OR_IF)) {
            Node *right = parse_pipeline(p);
            if (!right) {
                free_node(left);
                if (!p->err[0]) {
                    snprintf(p->err, sizeof(p->err), "expected command after ||");
                }
                return NULL;
            }
            left = node_bin(NODE_OR, left, right);
            continue;
        }
        break;
    }
    return left;
}

static Node *parse_list(Parser *p) {
    Node *result = NULL;
    Node *current = parse_and_or(p);
    if (!current) {
        return NULL;
    }

    while (1) {
        int sep = 0; /* 0 none, 1 ;, 2 & */
        if (p_match(p, TOK_SEMI)) {
            sep = 1;
            while (p_match(p, TOK_SEMI)) {
            }
        } else if (p_match(p, TOK_AMP)) {
            sep = 2;
        }

        Node *item = current;
        if (sep == 2) {
            item = node_bg(item);
        }
        if (!result) {
            result = item;
        } else {
            result = node_bin(NODE_SEQ, result, item);
        }

        if (sep == 0) {
            break;
        }

        if (!p_is_cmd_start(p_peek(p)->type)) {
            break;
        }

        current = parse_and_or(p);
        if (!current) {
            free_node(result);
            return NULL;
        }
    }

    return result;
}

static Node *parse_tokens(Token *toks, size_t ntok, char *err, size_t errsz) {
    Parser p;
    memset(&p, 0, sizeof(p));
    p.toks = toks;
    p.ntok = ntok;

    if (p_peek(&p)->type == TOK_EOF) {
        return NULL;
    }

    Node *root = parse_list(&p);
    if (!root) {
        if (!p.err[0]) {
            snprintf(err, errsz, "syntax error");
        } else {
            snprintf(err, errsz, "%s", p.err);
        }
        return NULL;
    }

    if (p_peek(&p)->type != TOK_EOF && p_peek(&p)->type != TOK_RPAREN) {
        snprintf(err, errsz, "unexpected token");
        free_node(root);
        return NULL;
    }

    if (p_peek(&p)->type == TOK_RPAREN) {
        snprintf(err, errsz, "unexpected ')' ");
        free_node(root);
        return NULL;
    }

    return root;
}

static void cmd_replace_argv(Node *cmd, char **nargv, int *nquoted, int nargc) {
    for (int i = 0; i < cmd->as.cmd.argc; i++) {
        free(cmd->as.cmd.argv[i]);
    }
    free(cmd->as.cmd.argv);
    free(cmd->as.cmd.quoted);
    cmd->as.cmd.argv = nargv;
    cmd->as.cmd.quoted = nquoted;
    cmd->as.cmd.argc = nargc;
    cmd->as.cmd.cap = nargc;
}

static void maybe_expand_alias(Node *cmd) {
    if (!cmd || cmd->type != NODE_CMD || cmd->as.cmd.argc == 0) {
        return;
    }

    for (int depth = 0; depth < 16; depth++) {
        int nassign = command_assignment_prefix(cmd->as.cmd.argv, cmd->as.cmd.argc);
        if (nassign >= cmd->as.cmd.argc) {
            return;
        }
        const char *av = alias_get(cmd->as.cmd.argv[nassign]);
        if (!av || !*av) {
            return;
        }

        TokenVec tv;
        memset(&tv, 0, sizeof(tv));
        char err[256] = {0};
        if (lex_line(av, &tv, err, sizeof(err)) != 0) {
            tv_free(&tv);
            return;
        }

        int wcount = 0;
        for (size_t i = 0; i < tv.len; i++) {
            if (tv.data[i].type == TOK_WORD) {
                wcount++;
                continue;
            }
            if (tv.data[i].type == TOK_EOF) {
                continue;
            }
            wcount = 0;
            break;
        }
        if (wcount == 0) {
            tv_free(&tv);
            return;
        }

        int rest = cmd->as.cmd.argc - (nassign + 1);
        int newc = nassign + wcount + rest;
        char **nargv = xmalloc(sizeof(char *) * (size_t)newc);
        int *nquoted = xmalloc(sizeof(int) * (size_t)newc);
        int at = 0;
        for (int i = 0; i < nassign; i++) {
            nargv[at] = xstrdup(cmd->as.cmd.argv[i]);
            nquoted[at] = cmd->as.cmd.quoted[i];
            at++;
        }
        for (size_t i = 0; i < tv.len; i++) {
            if (tv.data[i].type == TOK_WORD) {
                nargv[at] = xstrdup(tv.data[i].text ? tv.data[i].text : "");
                nquoted[at] = tv.data[i].quoted;
                at++;
            }
        }
        for (int i = nassign + 1; i < cmd->as.cmd.argc; i++) {
            nargv[at] = xstrdup(cmd->as.cmd.argv[i]);
            nquoted[at] = cmd->as.cmd.quoted[i];
            at++;
        }
        tv_free(&tv);
        cmd_replace_argv(cmd, nargv, nquoted, newc);
    }
}

static int status_to_code(int st) {
    if (WIFEXITED(st)) {
        return WEXITSTATUS(st);
    }
    if (WIFSIGNALED(st)) {
        return 128 + WTERMSIG(st);
    }
    if (WIFSTOPPED(st)) {
        return 128 + WSTOPSIG(st);
    }
    return st;
}

static Job *job_new(pid_t pgid, const char *cmdline, const pid_t *pids, int npids, pid_t last_pid) {
    Job *j = xmalloc(sizeof(Job));
    memset(j, 0, sizeof(*j));
    j->id = g_next_job_id++;
    j->pgid = pgid;
    j->cmdline = xstrdup(cmdline ? cmdline : "");
    j->procs = xmalloc(sizeof(ProcEntry) * (size_t)npids);
    j->nproc = npids;
    j->last_pid = last_pid;
    j->last_raw_status = 0;
    for (int i = 0; i < npids; i++) {
        j->procs[i].pid = pids[i];
        j->procs[i].state = PROC_RUNNING;
        j->procs[i].raw_status = 0;
    }
    j->next = NULL;
    return j;
}

static void job_add(Job *j) {
    j->next = g_jobs;
    g_jobs = j;
}

static int job_is_completed(const Job *j) {
    for (int i = 0; i < j->nproc; i++) {
        if (j->procs[i].state != PROC_DONE) {
            return 0;
        }
    }
    return 1;
}

static int job_is_stopped(const Job *j) {
    int any_stopped = 0;
    for (int i = 0; i < j->nproc; i++) {
        if (j->procs[i].state == PROC_RUNNING) {
            return 0;
        }
        if (j->procs[i].state == PROC_STOPPED) {
            any_stopped = 1;
        }
    }
    return any_stopped;
}

static Job *job_find_by_id(int id) {
    for (Job *j = g_jobs; j; j = j->next) {
        if (j->id == id) {
            return j;
        }
    }
    return NULL;
}

static Job *job_find_latest(void) {
    return g_jobs;
}

static void job_free(Job *j) {
    free(j->cmdline);
    free(j->procs);
    free(j);
}

static void job_remove(Job *j) {
    Job *prev = NULL;
    Job *cur = g_jobs;
    while (cur) {
        if (cur == j) {
            if (prev) {
                prev->next = cur->next;
            } else {
                g_jobs = cur->next;
            }
            job_free(cur);
            return;
        }
        prev = cur;
        cur = cur->next;
    }
}

static int mark_pid_status(pid_t pid, int status) {
    for (Job *j = g_jobs; j; j = j->next) {
        for (int i = 0; i < j->nproc; i++) {
            if (j->procs[i].pid == pid) {
                if (WIFSTOPPED(status)) {
                    j->procs[i].state = PROC_STOPPED;
                } else if (WIFCONTINUED(status)) {
                    j->procs[i].state = PROC_RUNNING;
                } else {
                    j->procs[i].state = PROC_DONE;
                }
                j->procs[i].raw_status = status;
                if (pid == j->last_pid) {
                    j->last_raw_status = status;
                }
                return 1;
            }
        }
    }
    return 0;
}

static const char *job_state_str(const Job *j) {
    if (job_is_completed(j)) {
        return "Done";
    }
    if (job_is_stopped(j)) {
        return "Stopped";
    }
    return "Running";
}

static void update_jobs(int notify) {
    int status;
    pid_t pid;
    while ((pid = waitpid(-1, &status, WNOHANG | WUNTRACED | WCONTINUED)) > 0) {
        mark_pid_status(pid, status);
    }

    Job *cur = g_jobs;
    Job *prev = NULL;
    while (cur) {
        Job *next = cur->next;
        if (job_is_completed(cur)) {
            if (notify) {
                fprintf(stderr, "[%d] Done\t%s\n", cur->id, cur->cmdline);
            }
            if (prev) {
                prev->next = next;
            } else {
                g_jobs = next;
            }
            job_free(cur);
            cur = next;
            continue;
        }

        if (job_is_stopped(cur)) {
            if (notify && !cur->notified) {
                fprintf(stderr, "[%d] Stopped\t%s\n", cur->id, cur->cmdline);
            }
            cur->notified = 1;
        } else {
            cur->notified = 0;
        }

        prev = cur;
        cur = next;
    }
}

static void reset_child_signals(void) {
    signal(SIGINT, SIG_DFL);
    signal(SIGQUIT, SIG_DFL);
    signal(SIGTSTP, SIG_DFL);
    signal(SIGTTIN, SIG_DFL);
    signal(SIGTTOU, SIG_DFL);
    signal(SIGCHLD, SIG_DFL);
}

static int ensure_saved_fd(SavedFD **head, int fd) {
    for (SavedFD *s = *head; s; s = s->next) {
        if (s->fd == fd) {
            return 0;
        }
    }
    SavedFD *s = xmalloc(sizeof(SavedFD));
    s->fd = fd;
    s->saved = dup(fd);
    if (s->saved < 0 && errno != EBADF) {
        free(s);
        return -1;
    }
    s->next = *head;
    *head = s;
    return 0;
}

static void restore_saved_fds(SavedFD *head) {
    SavedFD *s = head;
    while (s) {
        if (s->saved >= 0) {
            dup2(s->saved, s->fd);
            close(s->saved);
        } else {
            close(s->fd);
        }
        SavedFD *n = s->next;
        free(s);
        s = n;
    }
}

static int make_heredoc_fd(const char *delim) {
    int pfd[2];
    if (pipe(pfd) < 0) {
        perror("pipe");
        return -1;
    }

    char *line = NULL;
    size_t cap = 0;
    for (;;) {
        if (g_interactive) {
            fputs("heredoc> ", stderr);
            fflush(stderr);
        }
        ssize_t n = getline(&line, &cap, stdin);
        if (n < 0) {
            break;
        }

        size_t used = (size_t)n;
        if (used > 0 && line[used - 1] == '\n') {
            line[used - 1] = '\0';
            used--;
        }
        if (strcmp(line, delim) == 0) {
            break;
        }
        if (write(pfd[1], line, used) < 0 || write(pfd[1], "\n", 1) < 0) {
            perror("write");
            free(line);
            close(pfd[0]);
            close(pfd[1]);
            return -1;
        }
    }

    free(line);
    close(pfd[1]);
    return pfd[0];
}

static int apply_redirs(Redir *r, SavedFD **saved) {
    for (; r; r = r->next) {
        int fd = r->fd;
        if (fd < 0) {
            fd = (r->type == R_IN || r->type == R_HEREDOC) ? 0 : 1;
        }

        if (r->type == R_HEREDOC) {
            if (saved && ensure_saved_fd(saved, fd) < 0) {
                perror("dup");
                return -1;
            }
            int hfd = make_heredoc_fd(r->target);
            if (hfd < 0) {
                return -1;
            }
            if (dup2(hfd, fd) < 0) {
                perror("dup2");
                close(hfd);
                return -1;
            }
            close(hfd);
            continue;
        }

        if (r->type == R_DUP) {
            if (saved && ensure_saved_fd(saved, fd) < 0) {
                perror("dup");
                return -1;
            }
            if (dup2(r->dup_fd, fd) < 0) {
                perror("dup2");
                return -1;
            }
            continue;
        }

        if (r->type == R_OUT_ERR || r->type == R_APPEND_ERR) {
            if (saved && ensure_saved_fd(saved, STDOUT_FILENO) < 0) {
                perror("dup");
                return -1;
            }
            if (saved && ensure_saved_fd(saved, STDERR_FILENO) < 0) {
                perror("dup");
                return -1;
            }
            int oflags = O_WRONLY | O_CREAT;
            if (r->type == R_APPEND_ERR) {
                oflags |= O_APPEND;
            } else {
                oflags |= O_TRUNC;
            }
            int src = open(r->target, oflags, 0666);
            if (src < 0) {
                perror(r->target);
                return -1;
            }
            if (dup2(src, STDOUT_FILENO) < 0 || dup2(src, STDERR_FILENO) < 0) {
                perror("dup2");
                close(src);
                return -1;
            }
            close(src);
            continue;
        }

        if (saved && ensure_saved_fd(saved, fd) < 0) {
            perror("dup");
            return -1;
        }

        int oflags = 0;
        mode_t mode = 0666;
        int src = -1;

        if (r->type == R_IN) {
            oflags = O_RDONLY;
        } else if (r->type == R_OUT) {
            oflags = O_WRONLY | O_CREAT | O_TRUNC;
        } else {
            oflags = O_WRONLY | O_CREAT | O_APPEND;
        }

        src = open(r->target, oflags, mode);
        if (src < 0) {
            perror(r->target);
            return -1;
        }
        if (dup2(src, fd) < 0) {
            perror("dup2");
            close(src);
            return -1;
        }
        close(src);
    }
    return 0;
}

static int parse_int(const char *s, int *ok) {
    errno = 0;
    char *end = NULL;
    long v = strtol(s, &end, 10);
    if (errno != 0 || !end || *end != '\0') {
        *ok = 0;
        return 0;
    }
    *ok = 1;
    return (int)v;
}

static char *find_executable(const char *cmd) {
    if (!cmd || !*cmd) {
        return NULL;
    }
    if (strchr(cmd, '/')) {
        if (access(cmd, X_OK) == 0) {
            return xstrdup(cmd);
        }
        return NULL;
    }

    const char *path = getenv("PATH");
    if (!path || !*path) {
        path = "/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin";
    }
    char *dup = xstrdup(path);
    char *save = NULL;
    for (char *dir = strtok_r(dup, ":", &save); dir; dir = strtok_r(NULL, ":", &save)) {
        if (!*dir) {
            dir = ".";
        }
        size_t need = strlen(dir) + 1 + strlen(cmd) + 1;
        char *full = xmalloc(need);
        snprintf(full, need, "%s/%s", dir, cmd);
        if (access(full, X_OK) == 0) {
            free(dup);
            return full;
        }
        free(full);
    }
    free(dup);
    return NULL;
}

static int parse_assignment_word(const char *w, char **name_out, char **val_out) {
    const char *eq = strchr(w, '=');
    if (!eq || eq == w) {
        return 0;
    }
    size_t n = (size_t)(eq - w);
    char *name = xmalloc(n + 1);
    memcpy(name, w, n);
    name[n] = '\0';
    if (!valid_name(name)) {
        free(name);
        return 0;
    }
    *name_out = name;
    *val_out = xstrdup(eq + 1);
    return 1;
}

typedef struct {
    char *name;
    int had_old;
    char *old_value;
} TempAssign;

static int apply_temp_assignments(char **argv, int nassign, TempAssign **out) {
    TempAssign *ta = xmalloc(sizeof(*ta) * (size_t)nassign);
    memset(ta, 0, sizeof(*ta) * (size_t)nassign);
    for (int i = 0; i < nassign; i++) {
        char *name = NULL;
        char *val = NULL;
        if (!parse_assignment_word(argv[i], &name, &val)) {
            free(name);
            free(val);
            continue;
        }
        const char *old = getenv(name);
        ta[i].name = name;
        ta[i].had_old = old ? 1 : 0;
        ta[i].old_value = old ? xstrdup(old) : NULL;
        if (setenv(name, val, 1) < 0) {
            perror("setenv");
            free(val);
            for (int k = 0; k <= i; k++) {
                free(ta[k].name);
                free(ta[k].old_value);
            }
            free(ta);
            return -1;
        }
        free(val);
    }
    *out = ta;
    return 0;
}

static void restore_temp_assignments(TempAssign *ta, int nassign) {
    if (!ta) {
        return;
    }
    for (int i = 0; i < nassign; i++) {
        if (!ta[i].name) {
            continue;
        }
        if (ta[i].had_old) {
            setenv(ta[i].name, ta[i].old_value ? ta[i].old_value : "", 1);
        } else {
            unsetenv(ta[i].name);
        }
        free(ta[i].name);
        free(ta[i].old_value);
    }
    free(ta);
}

static int command_assignment_prefix(char **argv, int argc) {
    int i = 0;
    while (i < argc) {
        char *name = NULL;
        char *val = NULL;
        int ok = parse_assignment_word(argv[i], &name, &val);
        free(name);
        free(val);
        if (!ok) {
            break;
        }
        i++;
    }
    return i;
}

static void set_local_assignments(char **argv, int nassign) {
    for (int i = 0; i < nassign; i++) {
        char *name = NULL;
        char *val = NULL;
        if (!parse_assignment_word(argv[i], &name, &val)) {
            free(name);
            free(val);
            continue;
        }
        local_set(name, val);
        free(name);
        free(val);
    }
}

static int builtin_jobs(void) {
    update_jobs(0);
    for (Job *j = g_jobs; j; j = j->next) {
        fprintf(stdout, "[%d] %s\t%s\n", j->id, job_state_str(j), j->cmdline);
    }
    return 0;
}

static int wait_for_job(Job *j, int foreground) {
    if (foreground && g_interactive) {
        tcsetpgrp(g_shell_terminal, j->pgid);
    }

    while (!job_is_completed(j) && !job_is_stopped(j)) {
        int status;
        pid_t pid = waitpid(-j->pgid, &status, WUNTRACED);
        if (pid < 0) {
            if (errno == EINTR) {
                continue;
            }
            break;
        }
        mark_pid_status(pid, status);
    }

    if (foreground && g_interactive) {
        tcsetpgrp(g_shell_terminal, g_shell_pgid);
    }

    return status_to_code(j->last_raw_status);
}

static int builtin_fg(char **argv, int argc) {
    (void)argc;
    Job *j = NULL;
    if (argc > 1) {
        const char *spec = argv[1];
        if (*spec == '%') {
            spec++;
        }
        int ok = 0;
        int id = parse_int(spec, &ok);
        if (!ok) {
            fprintf(stderr, "fg: invalid job id\n");
            return 1;
        }
        j = job_find_by_id(id);
    } else {
        j = job_find_latest();
    }

    if (!j) {
        fprintf(stderr, "fg: no such job\n");
        return 1;
    }

    fprintf(stdout, "%s\n", j->cmdline);
    if (kill(-j->pgid, SIGCONT) < 0 && errno != ESRCH) {
        perror("fg: SIGCONT");
    }
    for (int i = 0; i < j->nproc; i++) {
        if (j->procs[i].state == PROC_STOPPED) {
            j->procs[i].state = PROC_RUNNING;
        }
    }

    int st = wait_for_job(j, 1);
    if (job_is_completed(j)) {
        job_remove(j);
    } else {
        fprintf(stderr, "[%d] Stopped\t%s\n", j->id, j->cmdline);
        j->notified = 1;
    }
    return st;
}

static int builtin_bg(char **argv, int argc) {
    Job *j = NULL;
    if (argc > 1) {
        const char *spec = argv[1];
        if (*spec == '%') {
            spec++;
        }
        int ok = 0;
        int id = parse_int(spec, &ok);
        if (!ok) {
            fprintf(stderr, "bg: invalid job id\n");
            return 1;
        }
        j = job_find_by_id(id);
    } else {
        j = job_find_latest();
    }

    if (!j) {
        fprintf(stderr, "bg: no such job\n");
        return 1;
    }

    if (kill(-j->pgid, SIGCONT) < 0 && errno != ESRCH) {
        perror("bg: SIGCONT");
        return 1;
    }
    for (int i = 0; i < j->nproc; i++) {
        if (j->procs[i].state == PROC_STOPPED) {
            j->procs[i].state = PROC_RUNNING;
        }
    }
    j->notified = 0;
    fprintf(stdout, "[%d] %d\n", j->id, (int)j->pgid);
    return 0;
}

static int builtin_cd(char **argv, int argc) {
    const char *target = NULL;
    if (argc < 2) {
        target = getenv("HOME");
        if (!target) {
            target = "/";
        }
    } else if (strcmp(argv[1], "-") == 0) {
        target = getenv("OLDPWD");
        if (!target) {
            fprintf(stderr, "cd: OLDPWD not set\n");
            return 1;
        }
        fprintf(stdout, "%s\n", target);
    } else {
        target = argv[1];
    }

    char oldpwd[4096];
    if (!getcwd(oldpwd, sizeof(oldpwd))) {
        oldpwd[0] = '\0';
    }

    if (chdir(target) < 0) {
        perror("cd");
        return 1;
    }

    if (oldpwd[0]) {
        setenv("OLDPWD", oldpwd, 1);
    }
    char cwd[4096];
    if (getcwd(cwd, sizeof(cwd))) {
        setenv("PWD", cwd, 1);
    }
    return 0;
}

static int builtin_export(char **argv, int argc) {
    if (argc == 1) {
        return 0;
    }
    for (int i = 1; i < argc; i++) {
        char *eq = strchr(argv[i], '=');
        if (!eq) {
            const char *v = lookup_var(argv[i]);
            if (!v) {
                v = "";
            }
            if (setenv(argv[i], v, 1) < 0) {
                perror("export");
                return 1;
            }
            continue;
        }
        size_t n = (size_t)(eq - argv[i]);
        char *name = xmalloc(n + 1);
        memcpy(name, argv[i], n);
        name[n] = '\0';
        if (setenv(name, eq + 1, 1) < 0) {
            perror("export");
            free(name);
            return 1;
        }
        local_set(name, eq + 1);
        free(name);
    }
    return 0;
}

static int builtin_unset(char **argv, int argc) {
    for (int i = 1; i < argc; i++) {
        if (unsetenv(argv[i]) < 0) {
            perror("unset");
            return 1;
        }
        local_unset(argv[i]);
    }
    return 0;
}

static int builtin_pwd(void) {
    char cwd[4096];
    if (!getcwd(cwd, sizeof(cwd))) {
        perror("pwd");
        return 1;
    }
    puts(cwd);
    return 0;
}

static int builtin_echo(char **argv, int argc) {
    int nflag = 0;
    int i = 1;
    if (i < argc && strcmp(argv[i], "-n") == 0) {
        nflag = 1;
        i++;
    }
    for (; i < argc; i++) {
        fputs(argv[i], stdout);
        if (i + 1 < argc) {
            fputc(' ', stdout);
        }
    }
    if (!nflag) {
        fputc('\n', stdout);
    }
    return 0;
}

static int builtin_history(void) {
    int start = shell_history_base();
    int end = start + shell_history_length();
    for (int idx = start; idx < end; idx++) {
        const char *line = shell_history_get_line(idx);
        if (line) {
            printf("%5d  %s\n", idx, line);
        }
    }
    return 0;
}

static int builtin_alias(char **argv, int argc) {
    if (argc == 1) {
        for (Alias *a = g_aliases; a; a = a->next) {
            printf("alias %s='%s'\n", a->name, a->value);
        }
        return 0;
    }

    int rc = 0;
    for (int i = 1; i < argc; i++) {
        char *eq = strchr(argv[i], '=');
        if (!eq) {
            const char *v = alias_get(argv[i]);
            if (!v) {
                fprintf(stderr, "alias: %s: not found\n", argv[i]);
                rc = 1;
                continue;
            }
            printf("alias %s='%s'\n", argv[i], v);
            continue;
        }
        size_t n = (size_t)(eq - argv[i]);
        char *name = xmalloc(n + 1);
        memcpy(name, argv[i], n);
        name[n] = '\0';
        if (!valid_name(name)) {
            fprintf(stderr, "alias: invalid name: %s\n", name);
            free(name);
            rc = 1;
            continue;
        }
        alias_set(name, eq + 1);
        free(name);
    }
    return rc;
}

static int builtin_type(char **argv, int argc) {
    if (argc < 2) {
        fprintf(stderr, "type: usage: type name ...\n");
        return 1;
    }
    int rc = 0;
    for (int i = 1; i < argc; i++) {
        const char *name = argv[i];
        const char *av = alias_get(name);
        if (av) {
            printf("%s is aliased to `%s`\n", name, av);
            continue;
        }
        if (is_builtin_name(name)) {
            printf("%s is a shell builtin\n", name);
            continue;
        }
        char *path = find_executable(name);
        if (path) {
            printf("%s is %s\n", name, path);
            free(path);
            continue;
        }
        fprintf(stderr, "type: %s: not found\n", name);
        rc = 1;
    }
    return rc;
}

static int builtin_which(char **argv, int argc) {
    if (argc < 2) {
        fprintf(stderr, "which: usage: which name ...\n");
        return 1;
    }
    int rc = 0;
    for (int i = 1; i < argc; i++) {
        char *path = find_executable(argv[i]);
        if (path) {
            puts(path);
            free(path);
            continue;
        }
        if (is_builtin_name(argv[i])) {
            printf("%s: shell built-in command\n", argv[i]);
            continue;
        }
        if (alias_get(argv[i])) {
            printf("%s: aliased\n", argv[i]);
            continue;
        }
        rc = 1;
    }
    return rc;
}

static int signal_by_name(const char *name) {
    if (!name || !*name) {
        return -1;
    }
    if (strncmp(name, "SIG", 3) == 0) {
        name += 3;
    }
    struct {
        const char *name;
        int sig;
    } sigs[] = {
        {"HUP", SIGHUP}, {"INT", SIGINT}, {"QUIT", SIGQUIT}, {"KILL", SIGKILL}, {"TERM", SIGTERM},
        {"STOP", SIGSTOP}, {"TSTP", SIGTSTP}, {"CONT", SIGCONT}, {"USR1", SIGUSR1}, {"USR2", SIGUSR2},
        {"PIPE", SIGPIPE}, {"ALRM", SIGALRM}, {"CHLD", SIGCHLD}
    };
    for (size_t i = 0; i < sizeof(sigs) / sizeof(sigs[0]); i++) {
        if (strcmp(name, sigs[i].name) == 0) {
            return sigs[i].sig;
        }
    }
    return -1;
}

static int builtin_kill(char **argv, int argc) {
    if (argc < 2) {
        fprintf(stderr, "kill: usage: kill [-SIGNAL] pid ...\n");
        return 1;
    }
    int sig = SIGTERM;
    int i = 1;
    if (argv[i][0] == '-' && argv[i][1]) {
        int ok = 0;
        int n = parse_int(argv[i] + 1, &ok);
        if (ok) {
            sig = n;
        } else {
            int s = signal_by_name(argv[i] + 1);
            if (s < 0) {
                fprintf(stderr, "kill: unknown signal: %s\n", argv[i]);
                return 1;
            }
            sig = s;
        }
        i++;
    }
    if (i >= argc) {
        fprintf(stderr, "kill: usage: kill [-SIGNAL] pid ...\n");
        return 1;
    }

    int rc = 0;
    for (; i < argc; i++) {
        int ok = 0;
        int pid = parse_int(argv[i], &ok);
        if (!ok) {
            fprintf(stderr, "kill: %s: invalid pid\n", argv[i]);
            rc = 1;
            continue;
        }
        if (kill((pid_t)pid, sig) < 0) {
            perror("kill");
            rc = 1;
        }
    }
    return rc;
}

static int run_builtin(char **argv, int argc, int in_main_shell) {
    if (argc == 0) {
        return 0;
    }

    if (strcmp(argv[0], "cd") == 0) {
        return builtin_cd(argv, argc);
    }
    if (strcmp(argv[0], "exit") == 0) {
        int code = g_last_status;
        if (argc > 1) {
            int ok = 0;
            code = parse_int(argv[1], &ok);
            if (!ok) {
                fprintf(stderr, "exit: numeric argument required\n");
                code = 2;
            }
        }
        g_should_exit = 1;
        g_exit_status = code;
        if (!in_main_shell) {
            return code;
        }
        return code;
    }
    if (strcmp(argv[0], "jobs") == 0) {
        return builtin_jobs();
    }
    if (strcmp(argv[0], "fg") == 0) {
        return builtin_fg(argv, argc);
    }
    if (strcmp(argv[0], "bg") == 0) {
        return builtin_bg(argv, argc);
    }
    if (strcmp(argv[0], "export") == 0) {
        return builtin_export(argv, argc);
    }
    if (strcmp(argv[0], "unset") == 0) {
        return builtin_unset(argv, argc);
    }
    if (strcmp(argv[0], "pwd") == 0) {
        return builtin_pwd();
    }
    if (strcmp(argv[0], "echo") == 0) {
        return builtin_echo(argv, argc);
    }
    if (strcmp(argv[0], "history") == 0) {
        return builtin_history();
    }
    if (strcmp(argv[0], "alias") == 0) {
        return builtin_alias(argv, argc);
    }
    if (strcmp(argv[0], "type") == 0) {
        return builtin_type(argv, argc);
    }
    if (strcmp(argv[0], "which") == 0) {
        return builtin_which(argv, argc);
    }
    if (strcmp(argv[0], "kill") == 0) {
        return builtin_kill(argv, argc);
    }
    if (strcmp(argv[0], "true") == 0) {
        return 0;
    }
    if (strcmp(argv[0], "false") == 0) {
        return 1;
    }

    return -1;
}

static int is_builtin_name(const char *s) {
    if (!s) {
        return 0;
    }
    for (int i = 0; g_builtin_names[i]; i++) {
        if (strcmp(s, g_builtin_names[i]) == 0) {
            return 1;
        }
    }
    return 0;
}

static int exec_node_shell(Node *n, const char *cmdline);

static char **make_exec_argv(char **argv, int argc, int offset) {
    int n = argc - offset;
    char **out = xmalloc(sizeof(char *) * (size_t)(n + 1));
    for (int i = 0; i < n; i++) {
        out[i] = argv[offset + i];
    }
    out[n] = NULL;
    return out;
}

static int exec_cmd_direct(Node *cmd, const char *cmdline) {
    (void)cmdline;
    maybe_expand_alias(cmd);

    if (apply_redirs(cmd->as.cmd.redirs, NULL) < 0) {
        return 1;
    }

    if (cmd->as.cmd.argc == 0) {
        return 0;
    }

    int nassign = command_assignment_prefix(cmd->as.cmd.argv, cmd->as.cmd.argc);
    if (nassign == cmd->as.cmd.argc) {
        for (int i = 0; i < nassign; i++) {
            char *name = NULL;
            char *val = NULL;
            if (parse_assignment_word(cmd->as.cmd.argv[i], &name, &val)) {
                setenv(name, val, 1);
            }
            free(name);
            free(val);
        }
        return 0;
    }

    TempAssign *ta = NULL;
    if (nassign > 0) {
        if (apply_temp_assignments(cmd->as.cmd.argv, nassign, &ta) < 0) {
            return 1;
        }
    }

    char **argv_exec = cmd->as.cmd.argv + nassign;
    int argc_exec = cmd->as.cmd.argc - nassign;
    int bi = run_builtin(argv_exec, argc_exec, 0);
    if (bi >= 0) {
        restore_temp_assignments(ta, nassign);
        return bi;
    }

    char **execv_argv = make_exec_argv(cmd->as.cmd.argv, cmd->as.cmd.argc, nassign);
    execvp(execv_argv[0], execv_argv);
    perror(execv_argv[0]);
    free(execv_argv);
    restore_temp_assignments(ta, nassign);
    return (errno == ENOENT) ? 127 : 126;
}

static int exec_subshell_direct(Node *sub, const char *cmdline) {
    if (apply_redirs(sub->as.subshell.redirs, NULL) < 0) {
        return 1;
    }
    return exec_node_shell(sub->as.subshell.child, cmdline);
}

static int exec_node_in_child(Node *n, const char *cmdline) {
    if (!n) {
        return 0;
    }
    if (n->type == NODE_CMD) {
        return exec_cmd_direct(n, cmdline);
    }
    if (n->type == NODE_SUBSHELL) {
        return exec_subshell_direct(n, cmdline);
    }
    return exec_node_shell(n, cmdline);
}

static int collect_pipeline(Node *n, Node ***arr, int *len, int *cap) {
    if (n->type == NODE_PIPE) {
        if (collect_pipeline(n->as.bin.left, arr, len, cap) < 0) {
            return -1;
        }
        if (collect_pipeline(n->as.bin.right, arr, len, cap) < 0) {
            return -1;
        }
        return 0;
    }

    if (*len == *cap) {
        *cap = *cap ? *cap * 2 : 8;
        *arr = xrealloc(*arr, sizeof(Node *) * (size_t)*cap);
    }
    (*arr)[(*len)++] = n;
    return 0;
}

static int launch_pipeline(Node *pipe_node, int background, const char *cmdline) {
    Node **parts = NULL;
    int n = 0;
    int cap = 0;
    if (collect_pipeline(pipe_node, &parts, &n, &cap) < 0 || n <= 0) {
        free(parts);
        return 1;
    }

    int *fds = NULL;
    if (n > 1) {
        fds = xmalloc(sizeof(int) * (size_t)(2 * (n - 1)));
        for (int i = 0; i < n - 1; i++) {
            if (pipe(&fds[2 * i]) < 0) {
                perror("pipe");
                free(fds);
                free(parts);
                return 1;
            }
        }
    }

    pid_t *pids = xmalloc(sizeof(pid_t) * (size_t)n);
    memset(pids, 0, sizeof(pid_t) * (size_t)n);
    pid_t pgid = 0;

    for (int i = 0; i < n; i++) {
        pid_t pid = fork();
        if (pid < 0) {
            perror("fork");
            free(parts);
            free(pids);
            if (fds) {
                for (int k = 0; k < 2 * (n - 1); k++) {
                    close(fds[k]);
                }
                free(fds);
            }
            return 1;
        }
        if (pid == 0) {
            reset_child_signals();
            if (pgid == 0) {
                setpgid(0, 0);
            } else {
                setpgid(0, pgid);
            }

            if (n > 1) {
                if (i > 0) {
                    if (dup2(fds[2 * (i - 1)], STDIN_FILENO) < 0) {
                        perror("dup2");
                        _exit(1);
                    }
                }
                if (i < n - 1) {
                    if (dup2(fds[2 * i + 1], STDOUT_FILENO) < 0) {
                        perror("dup2");
                        _exit(1);
                    }
                }
                for (int k = 0; k < 2 * (n - 1); k++) {
                    close(fds[k]);
                }
            }

            int st = exec_node_in_child(parts[i], cmdline);
            if (g_should_exit) {
                st = g_exit_status;
            }
            fflush(NULL);
            _exit(st);
        }

        if (pgid == 0) {
            pgid = pid;
        }
        setpgid(pid, pgid);
        pids[i] = pid;
    }

    if (fds) {
        for (int k = 0; k < 2 * (n - 1); k++) {
            close(fds[k]);
        }
        free(fds);
    }

    Job *j = job_new(pgid, cmdline, pids, n, pids[n - 1]);
    job_add(j);
    free(pids);
    free(parts);

    if (background) {
        g_last_bg = pgid;
        fprintf(stdout, "[%d] %d\n", j->id, (int)pgid);
        return 0;
    }

    int st = wait_for_job(j, 1);
    if (job_is_completed(j)) {
        job_remove(j);
    } else if (job_is_stopped(j)) {
        fprintf(stderr, "[%d] Stopped\t%s\n", j->id, j->cmdline);
        j->notified = 1;
    }
    return st;
}

static int launch_single(Node *n, int background, const char *cmdline) {
    pid_t pid = fork();
    if (pid < 0) {
        perror("fork");
        return 1;
    }

    if (pid == 0) {
        reset_child_signals();
        setpgid(0, 0);
        if (background) {
            int devnull = open("/dev/null", O_RDONLY);
            if (devnull >= 0) {
                dup2(devnull, STDIN_FILENO);
                close(devnull);
            }
        }
        int st = exec_node_in_child(n, cmdline);
        if (g_should_exit) {
            st = g_exit_status;
        }
        fflush(NULL);
        _exit(st);
    }

    setpgid(pid, pid);

    pid_t pids[1];
    pids[0] = pid;
    Job *j = job_new(pid, cmdline, pids, 1, pid);
    job_add(j);

    if (background) {
        g_last_bg = pid;
        fprintf(stdout, "[%d] %d\n", j->id, (int)pid);
        return 0;
    }

    int st = wait_for_job(j, 1);
    if (job_is_completed(j)) {
        job_remove(j);
    } else if (job_is_stopped(j)) {
        fprintf(stderr, "[%d] Stopped\t%s\n", j->id, j->cmdline);
        j->notified = 1;
    }
    return st;
}

static int run_builtin_parent(Node *cmd, int nassign) {
    SavedFD *saved = NULL;
    if (apply_redirs(cmd->as.cmd.redirs, &saved) < 0) {
        restore_saved_fds(saved);
        return 1;
    }
    TempAssign *ta = NULL;
    if (nassign > 0) {
        if (apply_temp_assignments(cmd->as.cmd.argv, nassign, &ta) < 0) {
            restore_saved_fds(saved);
            return 1;
        }
    }
    int st = run_builtin(cmd->as.cmd.argv + nassign, cmd->as.cmd.argc - nassign, 1);
    restore_temp_assignments(ta, nassign);
    restore_saved_fds(saved);
    return st;
}

static int run_empty_redir_parent(Node *cmd) {
    SavedFD *saved = NULL;
    if (apply_redirs(cmd->as.cmd.redirs, &saved) < 0) {
        restore_saved_fds(saved);
        return 1;
    }
    restore_saved_fds(saved);
    return 0;
}

static int exec_node_shell(Node *n, const char *cmdline) {
    if (!n) {
        return 0;
    }

    switch (n->type) {
        case NODE_SEQ: {
            int st = exec_node_shell(n->as.bin.left, cmdline);
            if (g_should_exit) {
                return st;
            }
            return exec_node_shell(n->as.bin.right, cmdline);
        }
        case NODE_AND: {
            int st = exec_node_shell(n->as.bin.left, cmdline);
            if (g_should_exit) {
                return st;
            }
            if (st == 0) {
                st = exec_node_shell(n->as.bin.right, cmdline);
            }
            return st;
        }
        case NODE_OR: {
            int st = exec_node_shell(n->as.bin.left, cmdline);
            if (g_should_exit) {
                return st;
            }
            if (st != 0) {
                st = exec_node_shell(n->as.bin.right, cmdline);
            }
            return st;
        }
        case NODE_BG:
            if (n->as.unary.child && n->as.unary.child->type == NODE_PIPE) {
                return launch_pipeline(n->as.unary.child, 1, cmdline);
            }
            return launch_single(n->as.unary.child, 1, cmdline);
        case NODE_PIPE:
            return launch_pipeline(n, 0, cmdline);
        case NODE_SUBSHELL:
            return launch_single(n, 0, cmdline);
        case NODE_CMD:
            maybe_expand_alias(n);
            if (n->as.cmd.argc == 0) {
                return run_empty_redir_parent(n);
            }
            {
                int nassign = command_assignment_prefix(n->as.cmd.argv, n->as.cmd.argc);
                if (nassign == n->as.cmd.argc) {
                    int st = run_empty_redir_parent(n);
                    if (st == 0) {
                        set_local_assignments(n->as.cmd.argv, nassign);
                    }
                    return st;
                }
                if (is_builtin_name(n->as.cmd.argv[nassign])) {
                    return run_builtin_parent(n, nassign);
                }
            }
            return launch_single(n, 0, cmdline);
    }

    return 1;
}

static void init_shell(void) {
    g_shell_terminal = STDIN_FILENO;
    g_interactive = isatty(g_shell_terminal);
    if (!g_interactive) {
        return;
    }

    while (tcgetpgrp(g_shell_terminal) != (g_shell_pgid = getpgrp())) {
        kill(-g_shell_pgid, SIGTTIN);
    }

    signal(SIGINT, SIG_IGN);
    signal(SIGQUIT, SIG_IGN);
    signal(SIGTSTP, SIG_IGN);
    signal(SIGTTIN, SIG_IGN);
    signal(SIGTTOU, SIG_IGN);

    g_shell_pgid = getpid();
    if (setpgid(g_shell_pgid, g_shell_pgid) < 0 && errno != EACCES && errno != EPERM) {
        perror("setpgid");
    }
    if (tcsetpgrp(g_shell_terminal, g_shell_pgid) < 0) {
        perror("tcsetpgrp");
    }
    if (tcgetattr(g_shell_terminal, &g_shell_tmodes) < 0) {
        perror("tcgetattr");
    }
}

static char *trim_line(const char *s) {
    size_t n = strlen(s);
    while (n > 0 && (s[n - 1] == '\n' || s[n - 1] == '\r')) {
        n--;
    }
    char *out = xmalloc(n + 1);
    memcpy(out, s, n);
    out[n] = '\0';
    return out;
}

static char *short_cwd(void) {
    char cwd[PATH_MAX];
    if (!getcwd(cwd, sizeof(cwd))) {
        return xstrdup("?");
    }
    const char *home = getenv("HOME");
    if (home && strncmp(cwd, home, strlen(home)) == 0 &&
        (cwd[strlen(home)] == '/' || cwd[strlen(home)] == '\0')) {
        size_t rest = strlen(cwd) - strlen(home);
        char *out = xmalloc(rest + 2);
        out[0] = '~';
        memcpy(out + 1, cwd + strlen(home), rest + 1);
        return out;
    }
    return xstrdup(cwd);
}

static char *build_prompt(void) {
    const char *user = getenv("USER");
    if (!user || !*user) {
        struct passwd *pw = getpwuid(getuid());
        user = pw ? pw->pw_name : "user";
    }
    char host[256] = {0};
    if (gethostname(host, sizeof(host) - 1) < 0) {
        snprintf(host, sizeof(host), "host");
    }
    char *cwd = short_cwd();
    size_t need = strlen(user) + strlen(host) + strlen(cwd) + 8;
    char *p = xmalloc(need);
    snprintf(p, need, "[%s@%s %s]$ ", user, host, cwd);
    free(cwd);
    return p;
}

static int line_is_complete(const char *line) {
    TokenVec tv;
    memset(&tv, 0, sizeof(tv));
    char err[256] = {0};
    if (lex_line(line, &tv, err, sizeof(err)) != 0) {
        if (strstr(err, "unterminated")) {
            tv_free(&tv);
            return 0;
        }
        tv_free(&tv);
        return 1;
    }

    int depth = 0;
    TokenType last = TOK_EOF;
    for (size_t i = 0; i < tv.len; i++) {
        TokenType t = tv.data[i].type;
        if (t == TOK_EOF) {
            continue;
        }
        last = t;
        if (t == TOK_LPAREN) {
            depth++;
        } else if (t == TOK_RPAREN) {
            depth--;
        }
    }
    tv_free(&tv);
    if (depth > 0) {
        return 0;
    }
    if (last == TOK_PIPE || last == TOK_AND_IF || last == TOK_OR_IF || last == TOK_REDIR || last == TOK_LPAREN) {
        return 0;
    }
    return 1;
}

static void sl_add_unique(char ***arr, int *len, int *cap, const char *s) {
    if (!s || !*s) {
        return;
    }
    for (int i = 0; i < *len; i++) {
        if (strcmp((*arr)[i], s) == 0) {
            return;
        }
    }
    if (*len == *cap) {
        *cap = *cap ? *cap * 2 : 32;
        *arr = xrealloc(*arr, sizeof(char *) * (size_t)*cap);
    }
    (*arr)[(*len)++] = xstrdup(s);
}

static void sl_free(char **arr, int len) {
    for (int i = 0; i < len; i++) {
        free(arr[i]);
    }
    free(arr);
}

static int starts_with(const char *s, const char *pref) {
    size_t n = strlen(pref);
    return strncmp(s, pref, n) == 0;
}

static char **g_comp_items = NULL;
static int g_comp_len = 0;
static int g_comp_idx = 0;

static void completion_reset_items(void) {
    sl_free(g_comp_items, g_comp_len);
    g_comp_items = NULL;
    g_comp_len = 0;
    g_comp_idx = 0;
}

static void completion_collect_commands(const char *text) {
    completion_reset_items();
    int cap = 0;

    for (int i = 0; g_builtin_names[i]; i++) {
        if (starts_with(g_builtin_names[i], text)) {
            sl_add_unique(&g_comp_items, &g_comp_len, &cap, g_builtin_names[i]);
        }
    }
    for (Alias *a = g_aliases; a; a = a->next) {
        if (starts_with(a->name, text)) {
            sl_add_unique(&g_comp_items, &g_comp_len, &cap, a->name);
        }
    }

    const char *path = getenv("PATH");
    if (!path || !*path) {
        path = "/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin";
    }
    char *dup = xstrdup(path);
    char *save = NULL;
    for (char *dir = strtok_r(dup, ":", &save); dir; dir = strtok_r(NULL, ":", &save)) {
        if (!*dir) {
            dir = ".";
        }
        DIR *dp = opendir(dir);
        if (!dp) {
            continue;
        }
        struct dirent *de;
        while ((de = readdir(dp)) != NULL) {
            if (de->d_name[0] == '.') {
                continue;
            }
            if (!starts_with(de->d_name, text)) {
                continue;
            }
            size_t need = strlen(dir) + 1 + strlen(de->d_name) + 1;
            char *full = xmalloc(need);
            snprintf(full, need, "%s/%s", dir, de->d_name);
            if (access(full, X_OK) == 0) {
                sl_add_unique(&g_comp_items, &g_comp_len, &cap, de->d_name);
            }
            free(full);
        }
        closedir(dp);
    }
    free(dup);
}

static char *command_generator(const char *text, int state) {
    if (state == 0) {
        completion_collect_commands(text);
        g_comp_idx = 0;
    }
    while (g_comp_idx < g_comp_len) {
        char *s = g_comp_items[g_comp_idx++];
        if (starts_with(s, text)) {
            return xstrdup(s);
        }
    }
    return NULL;
}

static void completion_collect_vars(const char *text) {
    completion_reset_items();
    int cap = 0;
    const char *pref = text[0] == '$' ? text + 1 : text;

    for (LocalVar *v = g_locals; v; v = v->next) {
        if (starts_with(v->name, pref)) {
            size_t need = strlen(v->name) + 2;
            char *cand = xmalloc(need);
            snprintf(cand, need, "$%s", v->name);
            sl_add_unique(&g_comp_items, &g_comp_len, &cap, cand);
            free(cand);
        }
    }

    extern char **environ;
    for (char **e = environ; e && *e; e++) {
        const char *eq = strchr(*e, '=');
        if (!eq) {
            continue;
        }
        size_t n = (size_t)(eq - *e);
        char *name = xmalloc(n + 1);
        memcpy(name, *e, n);
        name[n] = '\0';
        if (starts_with(name, pref)) {
            size_t need = n + 2;
            char *cand = xmalloc(need);
            snprintf(cand, need, "$%s", name);
            sl_add_unique(&g_comp_items, &g_comp_len, &cap, cand);
            free(cand);
        }
        free(name);
    }
}

static char *var_generator(const char *text, int state) {
    if (state == 0) {
        completion_collect_vars(text);
        g_comp_idx = 0;
    }
    while (g_comp_idx < g_comp_len) {
        char *s = g_comp_items[g_comp_idx++];
        if (starts_with(s, text)) {
            return xstrdup(s);
        }
    }
    return NULL;
}

#ifdef USE_READLINE
static char **shell_completion(const char *text, int start, int end) {
    (void)end;
    if (text[0] == '$') {
        rl_attempted_completion_over = 1;
        return rl_completion_matches(text, var_generator);
    }
    if (start == 0) {
        rl_attempted_completion_over = 1;
        return rl_completion_matches(text, command_generator);
    }
    rl_attempted_completion_over = 0;
    return NULL;
}
#endif

static void init_readline_support(void) {
#ifdef USE_READLINE
    rl_attempted_completion_function = shell_completion;
    rl_completion_append_character = ' ';
#endif
    shell_using_history();

    const char *home = getenv("HOME");
    if (!home || !*home) {
        return;
    }
    size_t need = strlen(home) + 32;
    g_history_path = xmalloc(need);
    snprintf(g_history_path, need, "%s/.myshell_history", home);
    shell_read_history(g_history_path);
    shell_stifle_history(5000);
}

static char *read_command_interactive(void) {
    StrBuf sb;
    sb_init(&sb);

    char *prompt = build_prompt();
    char *line = shell_readline(prompt);
    free(prompt);
    if (!line) {
        free(sb.buf);
        return NULL;
    }
    sb_adds(&sb, line);
    free(line);

    while (!line_is_complete(sb.buf ? sb.buf : "")) {
        char *cont = shell_readline("> ");
        if (!cont) {
            break;
        }
        sb_addc(&sb, '\n');
        sb_adds(&sb, cont);
        free(cont);
    }
    char *out = sb_take(&sb);
    if (*out) {
        shell_add_history(out);
    }
    return out;
}

static char *read_command_stream(FILE *in) {
    static char *line = NULL;
    static size_t cap = 0;

    StrBuf sb;
    sb_init(&sb);

    for (;;) {
        ssize_t nread = getline(&line, &cap, in);
        if (nread < 0) {
            if (sb.len == 0) {
                free(sb.buf);
                return NULL;
            }
            break;
        }
        char *trim = trim_line(line);
        if (sb.len > 0) {
            sb_addc(&sb, '\n');
        }
        sb_adds(&sb, trim);
        free(trim);
        if (line_is_complete(sb.buf ? sb.buf : "")) {
            break;
        }
    }
    return sb_take(&sb);
}

static int eval_cmdline(const char *cmdline) {
    TokenVec tv;
    memset(&tv, 0, sizeof(tv));
    char lex_err[256] = {0};
    if (lex_line(cmdline, &tv, lex_err, sizeof(lex_err)) != 0) {
        fprintf(stderr, "lex error: %s\n", lex_err[0] ? lex_err : "invalid input");
        g_last_status = 2;
        tv_free(&tv);
        return 2;
    }

    char parse_err[256] = {0};
    Node *root = parse_tokens(tv.data, tv.len, parse_err, sizeof(parse_err));
    if (!root) {
        if (parse_err[0]) {
            fprintf(stderr, "parse error: %s\n", parse_err);
            g_last_status = 2;
        }
        tv_free(&tv);
        return 2;
    }

    int st = exec_node_shell(root, cmdline);
    free_node(root);
    tv_free(&tv);
    return st;
}

int main(int argc, char **argv) {
    (void)argc;
    init_shell();
    shell_using_history();
    if (!g_interactive) {
        setvbuf(stdin, NULL, _IONBF, 0);
    }
    if (argv && argv[0]) {
        g_shell_path = xstrdup(argv[0]);
    }
    if (g_interactive) {
        init_readline_support();
    }

    while (!g_should_exit) {
        update_jobs(1);

        char *cmdline = g_interactive ? read_command_interactive() : read_command_stream(stdin);
        if (!cmdline) {
            if (g_interactive) {
                fputc('\n', stdout);
            }
            break;
        }
        if (!*cmdline) {
            free(cmdline);
            continue;
        }
        if (!g_interactive) {
            shell_add_history(cmdline);
        }

        int st = eval_cmdline(cmdline);
        if (g_should_exit) {
            g_last_status = g_exit_status;
        } else {
            g_last_status = st;
        }
        fflush(NULL);
        free(cmdline);
    }

    if (g_history_path) {
        shell_write_history(g_history_path);
    }

    completion_reset_items();
    shell_history_cleanup();
    free(g_shell_path);
    free(g_history_path);
    alias_free_all();
    local_free_all();

    while (g_jobs) {
        Job *n = g_jobs->next;
        job_free(g_jobs);
        g_jobs = n;
    }

    if (g_should_exit) {
        return g_exit_status;
    }
    return g_last_status;
}
