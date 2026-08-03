#!/usr/bin/env bash
# Run semantic-alignment baseline audits in parallel and produce a summary report.
set -uo pipefail

cd "$(dirname "$0")/.."
OUT="tmp/semantic_baseline"
REPORT="reports/SEMANTIC_ALIGNMENT_BASELINE_2026_08_02.md"
mkdir -p "$OUT"

echo "[start] semantic alignment baseline audit: $(date -Iseconds)"

run_audit() {
    local name="$1"
    shift
    echo "[run] $name"
    "$@" > "$OUT/${name}.log" 2>&1
    echo $? > "$OUT/${name}.rc"
}

# Launch audits in background
run_audit authority python scripts/check_concept_authority_coverage.py --strict --include-crates &
pid_auth=$!
run_audit version python scripts/check_version_semantic_injection.py --strict &
pid_ver=$!
run_audit cross_domain python scripts/check_cross_domain_coverage.py --strict &
pid_cross=$!
run_audit overlap python scripts/detect_content_overlap_v2.py --budget 999999 &
pid_overlap=$!
run_audit stub python scripts/check_stub_purity.py --strict &
pid_stub=$!
run_audit naming python scripts/check_naming_convention.py --strict &
pid_naming=$!
run_audit metadata python scripts/check_metadata_consistency.py --strict &
pid_meta=$!
run_audit codeblocks_stats python scripts/check_concept_code_blocks.py --stats-only &
pid_cb=$!

wait $pid_auth
wait $pid_ver
wait $pid_cross
wait $pid_overlap
wait $pid_stub
wait $pid_naming
wait $pid_meta
wait $pid_cb

echo "[done] audits finished; generating report"

python3 - "$OUT" "$REPORT" <<'PY'
import sys
from pathlib import Path

out_dir = Path(sys.argv[1])
report_path = Path(sys.argv[2])

audits = [
    ("authority", "Concept authority coverage (--include-crates)"),
    ("version", "Version semantic injection"),
    ("cross_domain", "Cross-domain semantic coverage"),
    ("overlap", "Content overlap v2"),
    ("stub", "Stub purity"),
    ("naming", "Naming convention"),
    ("metadata", "Metadata consistency"),
    ("codeblocks_stats", "Concept code blocks (stats-only)"),
]

lines = [
    "# 语义对齐基线审计报告",
    "",
    "**EN**: Semantic Alignment Baseline Audit Report",
    "**Summary**: Quantified baseline of concept authority, version injection, cross-domain coverage, overlap, stub purity, naming, metadata, and code-block health before the alignment sprint.",
    "",
    f"> 生成时间: {Path('.').resolve().stat().st_mtime if False else 'see file mtime'}",
    "",
    "| 审计项 | 退出码 | 日志 |",
    "|--------|--------|------|",
]

for key, title in audits:
    rc_file = out_dir / f"{key}.rc"
    log_file = out_dir / f"{key}.log"
    rc = rc_file.read_text().strip() if rc_file.exists() else "?"
    lines.append(f"| {title} | {rc} | `{log_file}` |")

lines += ["", "## 详细日志摘要（尾部）", ""]

for key, title in audits:
    log_file = out_dir / f"{key}.log"
    rc_file = out_dir / f"{key}.rc"
    rc = rc_file.read_text().strip() if rc_file.exists() else "?"
    lines.append(f"### {title} (rc={rc})")
    lines.append("")
    if log_file.exists():
        text = log_file.read_text(encoding="utf-8", errors="replace")
        tail = "\n".join(text.splitlines()[-80:])
        lines.append("```")
        lines.append(tail)
        lines.append("```")
    else:
        lines.append("*日志不存在*")
    lines.append("")

report_path.write_text("\n".join(lines), encoding="utf-8")
print(f"Wrote {report_path}")
PY

echo "[report] $REPORT"
