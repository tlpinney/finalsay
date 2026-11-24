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
# Ignored files are included (node_modules, build output, .env): a planted
# node_modules/.bin/x runs later just like a tracked file, so the undo has to
# cover it. That makes snapshots bigger, and secrets are copied into the store.
# Not covered: git repositories nested in the project (a directory below the root
# with its own .git) are stored as a pointer, not their files. The gate treats
# writes there as irreversible (file.write.nested-repo).
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
    g add -A -f             # -f: include ignored files too
    g commit -q --allow-empty -m "checkpoint $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    g rev-parse --short HEAD ;;
  list)
    g log --format='%h %s' ;;
  restore)
    g reset -q --hard "$rev"
    g clean -qfdx -e .git   # removes new files, ignored ones too; keeps the project's .git
    echo "restored $proj to $rev" ;;
  *)
    sed -n '2,17p' "$0"; exit 2 ;;
esac
