#!/usr/bin/env bash
# Run all quality gates locally.
# 14 blocking gates (10 Cargo/mdbook/KB/i18n/mermaid + 4 promoted semantic gates in --strict mode)
# + 6 semantic observe gates (warning, non-blocking).
#
# 观察门转正机制（见 AGENTS.md §5.2）：连续 4 周或连续 10 次 CI 运行达标后可评估转阻断。
# 2026-07-12 已转正（本地 --strict 实跑 exit=0）：topology / kg_shapes / canonical_uniqueness /
# concept_consistency_auditor。仍观察：metadata_consistency（D2=1/D5=17）、semantic_health、
# concept_authority_coverage（--strict 当前 exit=1：any=99.5%/none=2/core_gap=1）、overlap v2
# （可处理项 MERGE+DOCS_INTERNAL>0）、naming_convention（2026-07-12 新增，ERROR=0/WARN=85）。
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

# --- Content Overlap v2 (observe, actionable-baseline WARN escalation) ---
# 基线（2026-07-12 复测）：可处理项 = MERGE 5 + DOCS_INTERNAL 49 = 54（总命中 552，SERIES 24 白名单，REVIEW 474）。
# 注：MERGE 5 条目中 autoverus 对双向重复计数，去重后唯一对 4 + DOCS_INTERNAL 49 = 53（与 AGENTS.md §5.2 的 53 一致）；
#     2026-07-12 已在 triage_overlap.py 显式登记两对 SERIES 误报（c10 examples_collection/part2、c02 readme_rust_189/190）。
# 判定升级：可处理项 > 基线 ⇒ WARN 升级提示（新增重复，需先 triage 处置）；
#           可处理项 = 0     ⇒ 具备转阻断资格（届时改为 v2 --strict，可处理项>0 即 exit 1）。
# 当前仍为观察门：无论结果如何不置 FAILED。
OVERLAP_V2_ACTIONABLE_BASELINE=54
echo ""
echo "=== Content Overlap v2 (observe, actionable baseline=$OVERLAP_V2_ACTIONABLE_BASELINE) ==="
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
    echo "⚠️ WARN 升级: 可处理重复对 ($ACTIONABLE) 超过基线 ($OVERLAP_V2_ACTIONABLE_BASELINE) — 新增重复内容，请先 triage 处置（MERGE 合并 / DOCS_INTERNAL 互链）。"
elif [ "$ACTIONABLE" -eq 0 ]; then
    echo "✅ 可处理项=0 — 具备转阻断资格：可将本门改为 'python scripts/detect_content_overlap_v2.py --strict --budget 0'。"
else
    echo "✅ 可处理项 ($ACTIONABLE) 未超基线，维持观察。"
fi

echo ""
if [ "$FAILED" -eq 0 ]; then
    echo "✅ All 20 quality gates passed (14 blocking + 6 semantic observe)."
    exit 0
else
    echo "❌ Some quality gates failed."
    exit 1
fi
