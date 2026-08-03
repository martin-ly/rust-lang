#!/usr/bin/env python3
"""Split the mdbook-pandoc native output into chunks, render each chunk to PDF
with lualatex, then merge the chunk PDFs into the final book PDF."""

import os
import sys
import subprocess
from pathlib import Path


try:
    from pypdf import PdfWriter
except Exception as exc:  # pragma: no cover
    print(f"ERROR: pypdf is required for merging PDFs: {exc}", file=sys.stderr)
    sys.exit(1)

BASE = Path("E:/_src/rust-lang").resolve()
INPUTS_FILE = BASE / "book/pandoc/pdf/mdbook-pandoc-inputs.txt"
OUT_DIR = BASE / "book/pandoc/pdf"
FINAL_PDF = BASE / "book/rust-concept-knowledge-base.pdf"
HEADER = BASE / "pandoc-header.tex"

PANDOC = "pandoc"
WORKERS = 3
CHUNKS = 5


def read_inputs() -> list[str]:
    with open(INPUTS_FILE, "r", encoding="utf-8") as f:
        return [line.strip() for line in f if line.strip()]


def merge_native_files(paths: list[str], out_path: Path) -> None:
    inner_parts: list[str] = []
    for p in paths:
        src = BASE / p.replace("\\", "/")
        text = src.read_text(encoding="utf-8").strip()
        if not text:
            continue
        if text.startswith("[") and text.endswith("]"):
            text = text[1:-1].strip()
        if text:
            inner_parts.append(text)
    out_path.write_text("[\n" + ",\n".join(inner_parts) + "\n]\n", encoding="utf-8")


def render_chunk(idx: int, paths: list[str]) -> tuple[int, int, Path | None]:
    native = OUT_DIR / f"chunk{idx}.native"
    pdf = OUT_DIR / f"chunk{idx}.pdf"
    log = OUT_DIR / f"chunk{idx}.log"

    print(f"[chunk {idx}] merging {len(paths)} native files -> {native}")
    merge_native_files(paths, native)

    def rel_posix(p: Path) -> str:
        return str(p.relative_to(BASE).as_posix())

    cmd = [
        PANDOC,
        rel_posix(native),
        "-f", "native",
        "-t", "pdf",
        "--pdf-engine=lualatex",
        "--pdf-engine-opt=-interaction=nonstopmode",
        "--pdf-engine-opt=-halt-on-error",
        "-o", rel_posix(pdf),
        "--variable", "documentclass=report",
        "--variable", "lang=zh",
        f"--include-in-header={rel_posix(HEADER)}",
        "--toc",
        "--number-sections",
    ]

    print(f"[chunk {idx}] running pandoc -> {pdf}")
    with open(log, "w", encoding="utf-8") as lf:
        result = subprocess.run(cmd, cwd=BASE, stdout=lf, stderr=subprocess.STDOUT)

    if result.returncode != 0 or not pdf.exists() or pdf.stat().st_size == 0:
        print(f"[chunk {idx}] FAILED (rc={result.returncode}); see {log}")
        return idx, result.returncode, None

    print(f"[chunk {idx}] OK -> {pdf} ({pdf.stat().st_size} bytes)")
    return idx, 0, pdf


def merge_pdfs(pdfs: list[Path]) -> None:
    print(f"[merge] combining {len(pdfs)} chunk PDFs -> {FINAL_PDF}")
    writer = PdfWriter()
    for pdf in pdfs:
        writer.append(str(pdf))
    with open(FINAL_PDF, "wb") as f:
        writer.write(f)
    writer.close()
    print(f"[merge] final PDF: {FINAL_PDF} ({FINAL_PDF.stat().st_size} bytes)")


def main() -> int:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    inputs = read_inputs()
    total = len(inputs)
    print(f"[info] {total} input files, splitting into {CHUNKS} chunks ({WORKERS} parallel workers)")

    chunk_size = (total + CHUNKS - 1) // CHUNKS
    chunks = [
        (i + 1, inputs[i * chunk_size : (i + 1) * chunk_size])
        for i in range(CHUNKS)
    ]

    results: list[tuple[int, int, Path | None]] = []
    for idx, paths in chunks:
        results.append(render_chunk(idx, paths))

    results.sort(key=lambda r: r[0])
    failed = [(idx, rc) for idx, rc, pdf in results if rc != 0 or pdf is None]
    if failed:
        print("ERROR: the following chunks failed:", failed, file=sys.stderr)
        for idx, rc, pdf in results:
            log = OUT_DIR / f"chunk{idx}.log"
            print(f"  chunk {idx}: rc={rc} log={log}", file=sys.stderr)
        return 1

    pdfs = [pdf for _, _, pdf in results if pdf is not None]
    merge_pdfs(pdfs)
    return 0


if __name__ == "__main__":
    sys.exit(main())
