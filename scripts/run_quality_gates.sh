#!/usr/bin/env bash
# Run all quality gates locally.
# 23 blocking gates (10 Cargo/mdbook/KB/i18n/mermaid + 13 promoted semantic gates in --strict mode)
# + 4 semantic observe gates（观察机制保留，见下方观察段注释）。
#
# 观察门转正机制（见 AGENTS.md §5.2）：连续 4 周或连续 10 次 CI 运行达标后可评估转阻断。
# 2026-07-12 已转正（本地 --strict 实跑 exit=0）：topology / kg_shapes / canonical_uniqueness /
# concept_consistency_auditor / overlap v2（可处理项清零，见 reports/DEDUP_V2_ZERO_2026_07_12.md）。
# 2026-07-14 已转正（R4 评估 reports/OBSERVE_GATE_PROMOTION_REVIEW_R4_2026_07_14.md，--strict 实跑
# exit=0）：concept_authority_coverage（--strict --include-crates）/ examples_compile（--strict；
# 同步新增 CI job）/ naming_convention（--strict 仅卡 ERROR，WARN 不阻断）/ quiz_system（--strict）。
# 2026-07-14 已转正（用户指示全部转阻断；--strict 实跑 exit=0，见
# reports/GATE_FULL_BLOCKING_U1_2026_07_14.md）：metadata_consistency / concept_code_blocks
# （--strict 默认抽样）/ mindmap_coverage / semantic_health。
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

# --- Promoted semantic gates (blocking, --strict; promoted per AGENTS.md §5.2) ---
# 2026-07-12 转正：topology / kg_shapes / canonical_uniqueness / concept_consistency。
run_gate "Topology Quality (strict)" python scripts/check_topology_quality.py --strict
run_gate "KG SHACL Validation (strict)" python scripts/check_kg_shapes.py --strict
run_gate "Canonical Uniqueness (strict)" python scripts/check_canonical_uniqueness.py --strict
run_gate "Concept Consistency Audit (strict)" python scripts/concept_consistency_auditor.py --strict
# 2026-07-14 转正（R4 评估 reports/OBSERVE_GATE_PROMOTION_REVIEW_R4_2026_07_14.md，--strict 实跑 exit=0）：
# authority coverage（any=100%/none=0/核心缺口=0/crates 64/64=100%）、examples compile（失败 0）、
# naming convention（--strict 仅卡 ERROR>0，WARN 不阻断）、quiz system（检查 1-3 失败即阻断）。
run_gate "Concept Authority Coverage (strict)" python scripts/check_concept_authority_coverage.py --strict --include-crates
run_gate "Examples Compile Check (strict)" python scripts/check_examples_compile.py --strict
run_gate "Naming Convention (strict)" python scripts/check_naming_convention.py --strict
run_gate "Quiz System (strict)" python scripts/check_quiz_system.py --strict

# --- 2026-07-14 转正（用户指示全部转阻断；--strict 实跑 exit=0，
# 见 reports/GATE_FULL_BLOCKING_U1_2026_07_14.md）---
run_gate "Metadata Consistency (strict)" python scripts/check_metadata_consistency.py --strict
# concept/ 代码块编译实测（2026-07-13 独立门；提取 concept/ ```rust 块并分类；
# compile_fail 验证确实失败（E0xxx 校验 + editionNNNN fence）；std-only 候选 >300 按文件分层
# 抽样 300 块 rustc --edition 2024 编译（自动包 fn main）；--with-deps 用 target/debug/deps rmeta
# 做 --extern 实测依赖块（默认门内不启用，需先 cargo build）。
# --strict 时“应过但失败/标注腐烂”>0 exit 1；默认抽样保持门运行时长可控。
run_gate "Concept Code Blocks (strict)" python scripts/check_concept_code_blocks.py --strict
# 思维表征覆盖（2026-07-13 P4 挂入）：mindmap 率/反例率，--strict 基线 mindmap>=10%/反例>=40%。
run_gate "Mindmap Coverage (strict)" python scripts/check_mindmap_coverage.py --strict
run_gate "Semantic Health (strict)" python scripts/semantic_health.py --strict

# --- Semantic quality gates (observe / warning, non-blocking) ---
# 观察门机制保留（见 AGENTS.md §5.2）：当前 4 个观察门（O1/O2/O3/O4）。新增观察门时在此段挂载
# （默认 exit 0、不加 --strict、命名后缀 (observe)），达标后按 §5.2 流程转阻断。

run_gate "Stub Purity (observe)" python scripts/check_stub_purity.py
run_gate "Cross-Domain Coverage (observe)" python scripts/check_cross_domain_coverage.py
run_gate "KG Relation Precision (observe)" python scripts/check_kg_relation_precision.py
run_gate "Decision Tree rustc Error Code Coverage (observe)" python scripts/check_decision_trees.py

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
    echo "✅ All 23 quality gates passed (23 blocking + 4 semantic observe)."
    exit 0
else
    echo "❌ Some quality gates failed."
    exit 1
fi
