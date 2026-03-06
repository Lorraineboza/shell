# Shell

`Shell` — однофайловый shell на C (`shell.c`), который запускается в терминале macOS/Linux и поддерживает ключевые возможности интерактивной командной оболочки.

## Почему была ошибка `Undefined symbols ... readline/history`

Ошибка возникала, потому что код использует функции библиотеки `readline/history`, а команда сборки была просто:

```bash
cc shell.c
```

В этом случае линковщик не подключает `libreadline`, поэтому символы вроде `readline`, `add_history`, `history_get` не находятся.

В текущей версии проекта это исправлено так:

1. Shell собирается **без `readline`** (fallback-режим):
   - история и чтение строк работают через встроенную реализацию.
2. Shell собирается **с `readline`** (полный интерактив: Ctrl+R/Tab и т.д.) через флаг `-DUSE_READLINE`.

## Сборка

### 1) Без `readline` (гарантированно работает)

```bash
cc shell.c -o shell
```

### 2) С `readline` (рекомендуется для полноценного интерактива)

```bash
cc -DUSE_READLINE shell.c -lreadline -o shell
```

Если `readline` установлен через Homebrew, используйте явные пути:

```bash
cc -DUSE_READLINE shell.c \
  -I"$(brew --prefix readline)/include" \
  -L"$(brew --prefix readline)/lib" \
  -lreadline -o astrashell
```

## Запуск

```bash
./astrashell
```

## Prompt

Формат приглашения:

```text
[username@hostname cwd]$ 
```

Пример:

```text
[paul@posix ~/Documents/Playground]$ 
```

## Что поддерживает shell

- Внутренние команды:
  - `cd`, `pwd`, `export`, `unset`, `echo`, `exit`
  - `alias`, `history`, `type`, `which`
  - `kill`, `jobs`, `fg`, `bg`
  - `true`, `false`
- Внешние команды через `fork/exec` + поиск по `PATH`
- Операторы:
  - `;`, `&`, `&&`, `||`, `|`
- Перенаправления:
  - `>`, `>>`, `<`, `2>`, `2>>`, `2>&1`, `&>`, `>&`, `<<` (heredoc)
- Подстановки:
  - переменные: `$VAR`, `${VAR}`, `$?`, `$$`, `$!`
  - command substitution: `$(...)` и обратные кавычки `` `...` ``
- Кавычки и экранирование
- Globbing:
  - `*`, `?`, `[]`
- Job control:
  - фоновые задачи (`&`), `jobs`, `fg`, `bg`
- Сигналы:
  - `Ctrl+C`, `Ctrl+Z`, `Ctrl+D`
- История команд:
  - в режиме `USE_READLINE`: стрелки, `Ctrl+R`, Tab completion
  - без `USE_READLINE`: история хранится и доступна через builtin `history`
- Однострочные и многострочные команды

## Примеры

```bash
ls | grep ".c"
```

```bash
echo hello > out.txt
cat < out.txt
```

```bash
sleep 30 &
jobs
fg %1
```

```bash
cat << EOF
line 1
line 2
EOF
```

## История

По умолчанию файл истории:

```text
~/.myshell_history
```

## Ограничения

`AstraShell` — учебно-практический shell. Он покрывает большой набор возможностей, но не является 100% byte-to-byte клоном `bash/zsh` по всем edge-case POSIX-деталям.

## Файлы проекта

- `shell.c` — весь shell в одном C-файле
- `shell` - исполняемый файл
- `README.md` — документация

