#!/usr/bin/env bash
set -euo pipefail
root=$(git rev-parse --show-toplevel)
cd "$root"
lake build TauCeti.Algebra.Module.DiscreteValuationRing TauCeti.Algebra.Module.DiscreteValuationRing.ElementaryDivisors
lake env bash -euo pipefail -c '
  sources="$1/research/crystalline-lifts"
  outputs=$(mktemp -d)
  trap '\''rm -f -- "$outputs"/*.olean "$outputs"/*.olean.private "$outputs"/*.olean.server "$outputs"/*.ir; rmdir -- "$outputs"'\'' EXIT
  export LEAN_PATH="$outputs:$LEAN_PATH"
  cd "$sources"
  for module in IntegralEnvelope LossOfLifts SaturationTest InfiniteReadings DepthProfile FiniteProfile LocalCount; do
    lean -R "$sources" -o "$outputs/$module.olean" "$module.lean"
    printf "Checked %s\n" "$module"
  done
' _ "$root"
python3 research/crystalline-lifts/check-board.py
