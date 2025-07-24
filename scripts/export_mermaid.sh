#!/bin/bash
# Mermaid 图谱一键导出脚本
# 依赖：npm install -g @mermaid-js/mermaid-cli

set -e

MERMAID_CLI=\"mmdc\"
OUTPUT_DIR=docs/diagrams
mkdir -p "$OUTPUT_DIR"

# 批量查找并导出 mermaid 代码块
grep -rl '```mermaid' docs/ | while read -r file; do
  base=$(basename "$file" .md)
  # 提取 mermaid 代码块到临时文件
  awk '/```mermaid/{flag=1;next}/```/{flag=0}flag' "$file" > "/tmp/$base.mmd"
  # 导出 SVG
  $MERMAID_CLI -i "/tmp/$base.mmd" -o "$OUTPUT_DIR/$base.svg"
  # 导出 PNG
  $MERMAID_CLI -i "/tmp/$base.mmd" -o "$OUTPUT_DIR/$base.png"
  echo "导出: $OUTPUT_DIR/$base.svg, $OUTPUT_DIR/$base.png"
done

echo "所有 Mermaid 图谱已批量导出到 $OUTPUT_DIR/" 