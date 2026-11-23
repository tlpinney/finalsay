#!/bin/sh
# Does an outside checkpoint survive a sandboxed run that damages the project,
# and does restore bring the working tree back exactly?
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
export AGENT_CHECKPOINTS="$T/store"
mkdir -p "$T/proj/src" && cd "$T/proj" && git init -q
echo 'print("v1")' > src/app.py && echo "notes" > README.md
before=$(find . -path ./.git -prune -o -type f -print | sort | xargs shasum | shasum)
rev=$("$here/examples/pi/checkpoint.sh" save "$T/proj")
echo "checkpoint: $rev"
# Simulate a bad run inside the sandbox: edit, delete, and add files.
srt -s /dev/stdin -c 'echo "print(\"pwned\")" > src/app.py; rm README.md; echo junk > new.txt' <<JSON
{ "network": { "allowedDomains": [], "deniedDomains": [] },
  "filesystem": { "denyRead": [], "allowWrite": ["$T/proj"], "denyWrite": ["$T/proj/.git"] } }
JSON
echo "after the run: $(ls | tr '\n' ' ')"
# Can the sandbox reach the store at all? (It's outside allowWrite.)
srt -s /dev/stdin -c "rm -rf '$T/store' 2>/dev/null; [ -d '$T/store' ] && echo 'store: survived an attempted delete from the sandbox' || echo 'store: DELETED'" <<JSON
{ "network": { "allowedDomains": [], "deniedDomains": [] },
  "filesystem": { "denyRead": [], "allowWrite": ["$T/proj"], "denyWrite": [] } }
JSON
"$here/examples/pi/checkpoint.sh" restore "$rev" "$T/proj"
after=$(find . -path ./.git -prune -o -type f -print | sort | xargs shasum | shasum)
[ "$before" = "$after" ] && echo "working tree: identical to the checkpoint" || echo "working tree: DIFFERS"
git rev-parse --git-dir >/dev/null && echo "project .git: intact"
