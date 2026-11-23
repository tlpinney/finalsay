#!/bin/sh
# Checkpoints kept OUTSIDE the project, so sandboxed code can't destroy them.
# The undo can't live inside the thing it undoes.
#
#   checkpoint.sh save    [project]   snapshot the working tree (prints the id)
#   checkpoint.sh list    [project]
#   checkpoint.sh restore REV [project]
#
# Store: $AGENT_CHECKPOINTS (default ~/.agent-checkpoints), one shadow git
# repository per project path. The project's own .git is never touched.
# Note: the project's .gitignore applies, and anything not ignored (including
# secrets such as .env) is copied into the store.
set -eu
cmd=${1:-}; shift || true
rev=""
if [ "$cmd" = restore ]; then rev=${1:?usage: checkpoint.sh restore REV [project]}; shift; fi
proj=$(cd "${1:-.}" && pwd -P)
store=${AGENT_CHECKPOINTS:-$HOME/.agent-checkpoints}
id=$(printf %s "$proj" | shasum | cut -c1-12)
export GIT_DIR="$store/$id.git" GIT_WORK_TREE="$proj"
g() { git -c user.name=checkpoint -c user.email=checkpoint@localhost "$@"; }

init() {
  [ -d "$GIT_DIR" ] && return
  mkdir -p "$store"
  g init -q
  printf '.git\n' >> "$GIT_DIR/info/exclude"
  printf '%s\n' "$proj" > "$GIT_DIR/description"
}

case "$cmd" in
  save)
    init
    g add -A
    g commit -q --allow-empty -m "checkpoint $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    g rev-parse --short HEAD ;;
  list)
    g log --format='%h %s' ;;
  restore)
    g reset -q --hard "$rev"
    g clean -qfd            # removes new files; .git is excluded, so it stays
    echo "restored $proj to $rev" ;;
  *)
    sed -n '2,13p' "$0"; exit 2 ;;
esac
