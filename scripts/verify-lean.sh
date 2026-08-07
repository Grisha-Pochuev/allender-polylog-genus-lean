#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

echo "[1/4] Rejecting proof placeholders"
if grep -R -n -E '\b(sorry|admit)\b' --include='*.lean' Allender Allender.lean; then
  echo "Lean proof placeholders are not allowed."
  exit 1
fi

echo "[2/4] Building every imported project module"
lake build

echo "[3/4] Compiling the explicit axiom audit"
lake env lean Allender/AxiomAudit.lean

echo "[4/4] Replaying every project module with leanchecker"
while IFS= read -r olean; do
  module="${olean#.lake/build/lib/lean/}"
  module="${module%.olean}"
  module="${module//\//.}"
  echo "leanchecker $module"
  lake env leanchecker "$module"
done < <(find .lake/build/lib/lean/Allender -type f -name '*.olean' | sort)

echo "Lean verification completed successfully."
