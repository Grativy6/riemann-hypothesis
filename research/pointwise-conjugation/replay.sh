#!/usr/bin/env bash
set -euo pipefail
root=$(git rev-parse --show-toplevel)
cd "$root"
lake env bash -euo pipefail -c '
  sources="$1/research/pointwise-conjugation"
  temp=$(mktemp -d)
  trap '\''rm -f -- "$temp"/*.olean "$temp"/*.olean.private "$temp"/*.olean.server "$temp"/*.ir; rmdir -- "$temp"'\'' EXIT
  export LEAN_PATH="$temp:$LEAN_PATH"
  cd "$sources"
  for module in ReadingTransport Origin Recenter Counterexamples Triangle AffineMarks FiberCount; do
    lean -R "$sources" -o "$temp/$module.olean" "$module.lean"
    printf "Checked %s\n" "$module"
  done
' _ "$root"
