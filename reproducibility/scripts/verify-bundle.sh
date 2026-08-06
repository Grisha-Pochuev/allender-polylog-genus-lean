#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

echo "Checking committed-file integrity..."
sha256sum -c MANIFEST.sha256

if command -v latexmk >/dev/null 2>&1; then
  echo "latexmk found; rebuilding the manuscript..."
  bash scripts/build-paper.sh
else
  echo "latexmk not found; integrity verified, source rebuild skipped."
  echo "Install latexmk and texlive-latex-extra to perform the source build."
fi
