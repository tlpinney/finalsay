#!/bin/sh
# Try run-later config writes at root AND nested depth, via shell.
cd "$(dirname "$0")"
try() { if ( eval "$2" ) >/dev/null 2>&1; then echo "  allowed  $1"; else echo "  DENIED   $1"; fi; }
try "root .git/hooks/pre-commit"     'echo x > .git/hooks/pre-commit'
try "nested sub/.git/hooks/pre-commit" 'mkdir -p sub/.git/hooks 2>/dev/null; echo x > sub/.git/hooks/pre-commit'
try "root .codex/config.toml"        'mkdir -p .codex; echo x > .codex/config.toml'
try "nested sub/.codex/config.toml"  'mkdir -p sub/.codex; echo x > sub/.codex/config.toml'
try "nested a/b/.cursor/hooks.json"  'mkdir -p a/b/.cursor; echo x > a/b/.cursor/hooks.json'
try "nested x/.agents/hooks.json"    'mkdir -p x/.agents; echo x > x/.agents/hooks.json'
try ".GIT case nested sub/.GIT/x"    'mkdir -p sub/.GIT; echo x > sub/.GIT/x'
try "ordinary src/main.ts"           'mkdir -p src; echo x > src/main.ts'
try "write ~/wrapper-probe"          'echo x > ~/wrapper-probe'
echo "probe-done"
