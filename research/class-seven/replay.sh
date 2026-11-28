#!/usr/bin/env bash
# Run from any directory within this checkout after lake build.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
cd "$root"
lake env bash -euo pipefail -c '
  sources="$1/research/class-seven"
  build=$(mktemp -d)
  trap '\''rm -f -- "$build"/*.olean "$build"/*.olean.private "$build"/*.olean.server "$build"/*.ir; rmdir -- "$build"'\'' EXIT
  export LEAN_PATH="$build:$LEAN_PATH"
  cd "$sources"
  for name in CofinalSeven OrbitSpectrum FiniteReadings EulerReadings GeometricSpectrum; do
    lean -R "$sources" -o "$build/$name.olean" "$name.lean"
    printf "Checked %s\n" "$name"
  done
' _ "$root"
