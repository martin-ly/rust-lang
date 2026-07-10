#!/usr/bin/env bash
# Run all quality gates locally.
# 10 blocking gates (Cargo/mdbook/KB/i18n/mermaid) + 3 semantic observe gates (warning, non-blocking).
# Semantic gates default to warning mode (exit 0); append --strict to make them blocking.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

FAILED=0

run_gate() {
    local name="$1"
    shift
    echo ""
    echo "=== $name ==="
    if "$@"; then
        echo "✅ $name passed"
    else
        echo "❌ $name failed"
        FAILED=1
    fi
}

run_gate "Cargo Check" cargo check --workspace
run_gate "Cargo Test" cargo test --workspace --quiet
run_gate "Cargo Clippy" cargo clippy --workspace -- -D warnings
run_gate "Cargo Audit" cargo audit --no-fetch
run_gate "Cargo Vet" cargo vet --locked
run_gate "mdbook Build" mdbook build
run_gate "KB Auditor Link Check" python scripts/kb_auditor.py --link-check
run_gate "Content Overlap Detection" python scripts/detect_content_overlap.py
run_gate "i18n Term Coverage" python scripts/add_bilingual_annotations.py --mode check-only
run_gate "Mermaid Syntax Check" python scripts/check_mermaid_syntax.py

# --- Semantic quality gates (observe / warning, non-blocking) ---
run_gate "Metadata Consistency (observe)" python scripts/check_metadata_consistency.py
run_gate "Content Overlap v2 (observe)" python scripts/detect_content_overlap_v2.py --budget 999999
run_gate "Topology Quality (observe)" python scripts/check_topology_quality.py

echo ""
if [ "$FAILED" -eq 0 ]; then
    echo "✅ All 13 quality gates passed (10 blocking + 3 semantic observe)."
    exit 0
else
    echo "❌ Some quality gates failed."
    exit 1
fi
