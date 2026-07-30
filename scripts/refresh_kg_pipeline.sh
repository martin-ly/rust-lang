#!/usr/bin/env bash
# KG 刷新流水线（AGENTS.md §7 KG 刷新与谓词实例化）。
# 在新增 concept/ 权威页或执行 apply_renumber.py 重新生成 KG 后运行。
#
# 用法:
#   bash scripts/refresh_kg_pipeline.sh
#   bash scripts/refresh_kg_pipeline.sh --check   # 仅校验，不执行刷新

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

CHECK_ONLY=false
if [[ "${1:-}" == "--check" ]]; then
    CHECK_ONLY=true
fi

log() {
    echo "[KG-pipeline] $*"
}

if $CHECK_ONLY; then
    log "校验模式：执行 KG 形态与谓词精度检查..."
    python scripts/check_kg_shapes.py --strict
    python scripts/check_kg_relation_precision.py --strict
    log "✅ KG 校验通过。"
    exit 0
fi

log "步骤 1/5：生成 KG 实体索引..."
python scripts/generate_kg_index.py

log "步骤 2/5：生成 KG v3 关系图..."
python scripts/generate_kg_v3.py

log "步骤 3/5：应用语义谓词实例化..."
python scripts/apply_kg_semantic_predicates.py --all-batches --apply

log "步骤 4/5：兜底剩余通用关系到 relatedTo..."
python scripts/fallback_kg_generic_to_related.py --apply

log "步骤 5/5：压缩 relatedTo 为具体目录/层启发式谓词..."
python scripts/compress_kg_relatedto.py --apply

log "执行最终校验..."
python scripts/check_kg_shapes.py --strict
python scripts/check_kg_relation_precision.py --strict

log "✅ KG 刷新流水线完成。"
