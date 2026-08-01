#!/usr/bin/env python3
"""Merge mdbook-pandoc native-format inputs into a single file and render PDF.

Workaround for Windows command-line length limit when invoking pandoc with
hundreds of input files.
"""
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BUILD_DIR = ROOT / "book"
PDF_DIR = BUILD_DIR / "pandoc" / "pdf"
RESPONSE_FILE = PDF_DIR / "mdbook-pandoc-inputs.txt"
MERGED_FILE = PDF_DIR / "merged.native"
OUTPUT_PDF = BUILD_DIR / "rust-concept-knowledge-base.pdf"


def merge_native_files() -> None:
    if not RESPONSE_FILE.exists():
        print(f"Response file not found: {RESPONSE_FILE}", file=sys.stderr)
        sys.exit(1)

    inputs = [line.strip() for line in RESPONSE_FILE.read_text(encoding="utf-8").splitlines() if line.strip()]
    inner_parts = []
    for inp in inputs:
        # Response file paths are relative to the project root (e.g., book\pandoc\pdf\src\...).
        path = ROOT / inp
        if not path.exists():
            print(f"Warning: input file not found: {path}", file=sys.stderr)
            continue
        text = path.read_text(encoding="utf-8").strip()
        if not text:
            continue
        if text.startswith("[") and text.endswith("]"):
            text = text[1:-1].strip()
        if text:
            inner_parts.append(text)

    merged = "[\n" + ",\n".join(inner_parts) + "\n]\n"
    MERGED_FILE.write_text(merged, encoding="utf-8")
    print(f"Merged {len(inner_parts)} native files into {MERGED_FILE}")


def render_pdf() -> None:
    pandoc = os.environ.get("PANDOC", "pandoc")
    xelatex = os.environ.get("PDF_ENGINE", "xelatex")
    cmd = [
        pandoc,
        str(MERGED_FILE),
        "-f", "native",
        "-t", "pdf",
        "--pdf-engine", xelatex,
        "-o", str(OUTPUT_PDF),
        "--variable", "documentclass=report",
        "--variable", "lang=zh",
        "--include-in-header", str(ROOT / "pandoc-header.tex"),
        "--toc",
        "--number-sections",
    ]
    print("Running:", " ".join(cmd))
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        print("Pandoc failed:", file=sys.stderr)
        print(result.stderr, file=sys.stderr)
        sys.exit(result.returncode)
    print(f"Wrote PDF: {OUTPUT_PDF}")


if __name__ == "__main__":
    merge_native_files()
    render_pdf()
