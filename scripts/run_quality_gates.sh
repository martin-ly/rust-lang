#!/usr/bin/env bash
# Run all quality gates locally.
# 15 blocking gates (10 Cargo/mdbook/KB/i18n/mermaid + 5 promoted semantic gates in --strict mode)
# + 5 semantic observe gates (warning, non-blocking).
#
# 观察门转正机制（见 AGENTS.md §5.2）：连续 4 周或连续 10 次 CI 运行达标后可评估转阻断。
# 2026-07-12 已转正（本地 --strict 实跑 exit=0）：topology / kg_shapes / canonical_uniqueness /
# concept_consistency_auditor / overlap v2（可处理项清零，见 reports/DEDUP_V2_ZERO_2026_07_12.md）。
# 仍观察：metadata_consistency（D2=1/D5=17）、semantic_health、concept_authority_coverage
# （--strict 当前 exit=1：any=99.5%/none=2/core_gap=1）、naming_convention（2026-07-12 新增，
# ERROR=0/WARN=85）。
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

# --- Blocking gates (10) ---
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

# --- Promoted semantic gates (blocking, --strict; promoted 2026-07-12 per AGENTS.md §5.2) ---
run_gate "Topology Quality (strict)" python scripts/check_topology_quality.py --strict
run_gate "KG SHACL Validation (strict)" python scripts/check_kg_shapes.py --strict
run_gate "Canonical Uniqueness (strict)" python scripts/check_canonical_uniqueness.py --strict
run_gate "Concept Consistency Audit (strict)" python scripts/concept_consistency_auditor.py --strict

# --- Semantic quality gates (observe / warning, non-blocking) ---
run_gate "Metadata Consistency (observe)" python scripts/check_metadata_consistency.py
run_gate "Concept Authority Coverage (observe)" python scripts/check_concept_authority_coverage.py
run_gate "Semantic Health (observe)" python scripts/semantic_health.py
run_gate "Examples Compile Check (observe)" python scripts/check_examples_compile.py
run_gate "Naming Convention (observe)" python scripts/check_naming_convention.py

# --- Content Overlap v2 (blocking, promoted 2026-07-12 per AGENTS.md §5.2) ---
# 转正依据：2026-07-12 可处理项清零（原 MERGE 5 + DOCS_INTERNAL 49 = 54 → 0）：
#   autoverus 近克隆对（双向计数 2）按 canonical 裁定差异化改写——L4 概念权威页保留、L7 改为
#   预览跟踪页（reports/DEDUP_V2_ZERO_2026_07_12.md）；其余 52 对经逐对人工复核登记 SERIES
#   白名单（docs/05_practice 项目指南系列 48 对 + design_theory 子目录索引系列 4 对，证据注释见
#   scripts/triage_overlap.py SERIES_PATH_RE）。
# 判定：可处理项（MERGE+DOCS_INTERNAL）> 基线 0 ⇒ FAILED=1（阻断）。
OVERLAP_V2_ACTIONABLE_BASELINE=0
echo ""
echo "=== Content Overlap v2 (blocking, actionable baseline=$OVERLAP_V2_ACTIONABLE_BASELINE) ==="
python scripts/detect_content_overlap_v2.py --budget 999999
python scripts/triage_overlap.py
ACTIONABLE=$(python - <<'EOF'
import glob, json
p = sorted(glob.glob("reports/OVERLAP_TRIAGE_*.json"))[-1]
s = json.load(open(p, encoding="utf-8"))["summary"]
print(s.get("MERGE", 0) + s.get("DOCS_INTERNAL", 0))
EOF
)
echo "[overlap-v2] actionable (MERGE+DOCS_INTERNAL) = $ACTIONABLE (baseline $OVERLAP_V2_ACTIONABLE_BASELINE)"
if [ "$ACTIONABLE" -gt "$OVERLAP_V2_ACTIONABLE_BASELINE" ]; then
    echo "❌ overlap-v2 可处理重复对 ($ACTIONABLE) > 基线 ($OVERLAP_V2_ACTIONABLE_BASELINE) — 阻断。请先 triage 处置：MERGE 合并/stub、DOCS_INTERNAL 合并/互链/登记 SERIES 白名单（附证据）。"
    FAILED=1
else
    echo "✅ overlap-v2 可处理项=0。"
fi

echo ""
if [ "$FAILED" -eq 0 ]; then
    echo "✅ All 20 quality gates passed (15 blocking + 5 semantic observe)."
    exit 0
else
    echo "❌ Some quality gates failed."
    exit 1
fi
