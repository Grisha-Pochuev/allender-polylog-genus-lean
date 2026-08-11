#!/usr/bin/env python3
"""Verify the SHA-256 integrity manifest for the Allender v_4.0 bundle.

This script is a reproducibility utility only. It is not part of the
mathematical proof and uses only the Python standard library.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
MANIFEST = ROOT / "MANIFEST_v_4.0.sha256"


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> int:
    if not MANIFEST.is_file():
        print(f"ERROR: missing manifest: {MANIFEST.name}")
        return 2

    failures = 0
    checked = 0
    for raw in MANIFEST.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        try:
            expected, filename = line.split(None, 1)
        except ValueError:
            print(f"ERROR: malformed manifest line: {raw!r}")
            failures += 1
            continue
        filename = filename.lstrip("* ")
        path = ROOT / filename
        checked += 1
        if not path.is_file():
            print(f"MISSING  {filename}")
            failures += 1
            continue
        actual = sha256_file(path)
        if actual != expected:
            print(f"FAILED   {filename}")
            print(f"  expected {expected}")
            print(f"  actual   {actual}")
            failures += 1
        else:
            print(f"OK       {filename}")

    if failures:
        print(f"\nIntegrity check failed: {failures} problem(s), {checked} entry/entries checked.")
        return 1
    print(f"\nIntegrity check passed: {checked} file(s) verified.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
