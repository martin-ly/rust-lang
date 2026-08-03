#!/usr/bin/env bash
# Render the mdbook-pandoc native output in chunks and merge into a single PDF.
set -euo pipefail

cd "$(dirname "$0")/.."
export PATH="$PATH:/c/Users/luyan/AppData/Local/Pandoc:/c/Users/luyan/AppData/Roaming/TinyTeX/bin/windows"

INPUTS="book/pandoc/pdf/mdbook-pandoc-inputs.txt"
PDF_DIR="book/pandoc/pdf"
FINAL="book/rust-concept-knowledge-base.pdf"
CHUNKS=5

echo "[merge] splitting ${INPUTS} into ${CHUNKS} native chunks..."
python3 -u - <<PY
from pathlib import Path
base = Path('.').resolve()
inputs_file = base / "${INPUTS}"
out_dir = base / "${PDF_DIR}"
out_dir.mkdir(parents=True, exist_ok=True)
with open(inputs_file, 'r', encoding='utf-8') as f:
    inputs = [ln.strip() for ln in f if ln.strip()]
chunk_size = (len(inputs) + ${CHUNKS} - 1) // ${CHUNKS}
for i in range(${CHUNKS}):
    chunk = inputs[i*chunk_size:(i+1)*chunk_size]
    parts = []
    for p in chunk:
        src = base / p.replace('\\', '/')
        text = src.read_text(encoding='utf-8').strip()
        if not text:
            continue
        if text.startswith('[') and text.endswith(']'):
            text = text[1:-1].strip()
        if text:
            parts.append(text)
    out = out_dir / f"chunk{i+1}.native"
    out.write_text('[\n' + ',\n'.join(parts) + '\n]\n', encoding='utf-8')
    print(f'[chunk {i+1}] {len(chunk)} files -> {out}')
PY

for i in $(seq 1 ${CHUNKS}); do
    native="${PDF_DIR}/chunk${i}.native"
    pdf="${PDF_DIR}/chunk${i}.pdf"
    log="${PDF_DIR}/chunk${i}.log"
    echo "[chunk ${i}] rendering ${pdf}..."
    pandoc "${native}" -f native -t pdf \
        --pdf-engine=lualatex \
        --pdf-engine-opt=-interaction=nonstopmode \
        --pdf-engine-opt=-halt-on-error \
        -o "${pdf}" \
        --variable documentclass=report \
        --variable lang=zh \
        --include-in-header=pandoc-header.tex \
        --toc --number-sections > "${log}" 2>&1
    if [ ! -s "${pdf}" ]; then
        echo "[chunk ${i}] FAILED; see ${log}"
        tail -n 40 "${log}"
        exit 1
    fi
    echo "[chunk ${i}] OK -> ${pdf} ($(du -h "${pdf}" | cut -f1))"
done

echo "[merge] combining ${CHUNKS} chunk PDFs -> ${FINAL}"
python3 - <<PY
from pathlib import Path
from pypdf import PdfWriter
base = Path('.').resolve()
pdf_dir = base / "${PDF_DIR}"
writer = PdfWriter()
for i in range(1, ${CHUNKS}+1):
    chunk = pdf_dir / f"chunk{i}.pdf"
    writer.append(str(chunk))
final = base / "${FINAL}"
with open(final, 'wb') as f:
    writer.write(f)
writer.close()
print(f'[merge] final PDF: {final} ({final.stat().st_size} bytes)')
PY

echo "[done] ${FINAL}"
