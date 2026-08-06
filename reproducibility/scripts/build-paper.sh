#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOURCE="$ROOT/paper/allender_polylog_genus_acc0_proof.tex"
OUTDIR="$ROOT/build"

if ! command -v latexmk >/dev/null 2>&1; then
  echo "latexmk is required. On Ubuntu install: sudo apt-get install latexmk texlive-latex-extra" >&2
  exit 2
fi

mkdir -p "$OUTDIR"
latexmk \
  -pdf \
  -interaction=nonstopmode \
  -halt-on-error \
  -file-line-error \
  -outdir="$OUTDIR" \
  "$SOURCE"

echo "Built: $OUTDIR/allender_polylog_genus_acc0_proof.pdf"
