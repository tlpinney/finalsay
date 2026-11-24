#!/bin/sh
# Does srt enforce the generated outer policy the way FinalSay/SrtConfig.lean
# assumes? For every run-later name in the settings: a write at the root, nested
# two levels down, and in upper case must be DENIED (and the file must not exist
# afterwards). A name is tested as a directory (name/x); a pattern with a wildcard
# (`*.pem`) is tested as a file (probe.pem). Writes to /tmp and $HOME must be denied; an ordinary project write
# must be allowed. Exits non-zero on any mismatch.
#
#   experiments/wrapper/probe.sh [settings.json]     (inside `nix develop`)
set -eu
here=$(cd "$(dirname "$0")" && pwd)
settings=${1:-$here/srt-outer.json}
settings=$(cd "$(dirname "$settings")" && pwd)/$(basename "$settings")
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
proj="$T/proj"; mkdir -p "$proj"; cd "$proj"; git init -q
# "PROJ" in the settings stands for the project directory.
sed "s#\"PROJ\"#\"$proj\"#" "$settings" > "$T/settings.json"
names=$(grep -o '"\*\*/[^"]*"' "$settings" | sed 's#^"\*\*/##; s#"$##')

script="$T/probe.sh"
: > "$script"
paths_for() {   # the three probe paths for one deny entry
  case "$1" in
    *'*'*) f=$(printf %s "$1" | sed 's/\*/probe/g')
           printf '%s\n' "$f" "a/b/$f" "$(printf %s "$f" | tr '[:lower:]' '[:upper:]')" ;;
    *)     printf '%s\n' "$1/x" "a/b/$1/x" "$(printf %s "$1" | tr '[:lower:]' '[:upper:]')/x" ;;
  esac
}
for n in $names; do
  for p in $(paths_for "$n"); do
    printf 'if (mkdir -p "%s" && echo x > "%s") 2>/dev/null; then echo "allowed %s"; else echo "denied %s"; fi\n' \
      "$(dirname "$p")" "$p" "$p" "$p" >> "$script"
  done
done
stamp=$$
cat >> "$script" <<SH
if (echo x > /tmp/probe-$stamp) 2>/dev/null; then echo "allowed /tmp"; else echo "denied /tmp"; fi
if (echo x > "\$HOME/probe-$stamp") 2>/dev/null; then echo "allowed HOME"; else echo "denied HOME"; fi
if (mkdir -p src && echo x > src/main.ts) 2>/dev/null; then echo "allowed src/main.ts"; else echo "denied src/main.ts"; fi
SH

out=$(srt -s "$T/settings.json" -c "sh '$script'" 2>/dev/null || true)
bad=0; total=0
paths_for() {   # the three probe paths for one deny entry
  case "$1" in
    *'*'*) f=$(printf %s "$1" | sed 's/\*/probe/g')
           printf '%s\n' "$f" "a/b/$f" "$(printf %s "$f" | tr '[:lower:]' '[:upper:]')" ;;
    *)     printf '%s\n' "$1/x" "a/b/$1/x" "$(printf %s "$1" | tr '[:lower:]' '[:upper:]')/x" ;;
  esac
}
for n in $names; do
  for p in $(paths_for "$n"); do
    total=$((total + 1))
    if printf '%s\n' "$out" | grep -qx "denied $p" && [ ! -e "$p" ]; then :; else
      echo "  FAIL  $p was not denied"; bad=$((bad + 1)); fi
  done
done
for want in "denied /tmp" "denied HOME" "allowed src/main.ts"; do
  total=$((total + 1))
  printf '%s\n' "$out" | grep -qx "$want" || { echo "  FAIL  expected: $want"; bad=$((bad + 1)); }
done
rm -f "/tmp/probe-$stamp" "$HOME/probe-$stamp"
echo "$((total - bad))/$total probes as expected ($(echo $names | wc -w | tr -d ' ') run-later names x root, nested, upper case; /tmp; \$HOME; ordinary write)"
[ "$bad" -eq 0 ]
