#!/usr/bin/env python3
"""Split the mdbook-pandoc native output into chunks, render each chunk to PDF
with lualatex, then merge the chunk PDFs into the final book PDF."""

import os
import sys
import subprocess
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed

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
    with open(out_path, "wb") as out:
        for p in paths:
            src = BASE / p.replace("\\", "/")
            with open(src, "rb") as src_f:
                out.write(src_f.read())
                out.write(b"\n")


def render_chunk(idx: int, paths: list[str]) -> tuple[int, int, Path | None]:
    native = OUT_DIR / f"chunk{idx}.native"
    pdf = OUT_DIR / f"chunk{idx}.pdf"
    log = OUT_DIR / f"chunk{idx}.log"

    print(f"[chunk {idx}] merging {len(paths)} native files -> {native}")
    merge_native_files(paths, native)

    cmd = [
        PANDOC,
        str(native),
        "-f", "native",
        "-t", "pdf",
        "--pdf-engine=lualatex",
        "--pdf-engine-opt=-interaction=nonstopmode",
        "--pdf-engine-opt=-halt-on-error",
        "-o", str(pdf),
        "--variable", "documentclass=report",
        "--variable", "lang=zh",
        f"--include-in-header={HEADER}",
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
    with ProcessPoolExecutor(max_workers=WORKERS) as ex:
        futures = {ex.submit(render_chunk, idx, paths): idx for idx, paths in chunks}
        for future in as_completed(futures):
            results.append(future.result())

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
