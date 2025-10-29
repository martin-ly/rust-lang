#!/bin/bash
# 占位符文件标注脚本
# 用法: ./mark_placeholders.sh

set -e

FORMAL_SYSTEM_DIR="$(cd "$(dirname "$0")" && pwd)"
MARKER="⚠️ **待完善**"
PLACEHOLDER_PATTERNS=(
    "待完善"
    "待创建"
    "TODO"
    "FIXME"
    "PLACEHOLDER"
    "TBD"
)

echo "🔍 搜索占位符文件..."
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

cd "$FORMAL_SYSTEM_DIR"

# 统计计数器
total_files=0
marked_files=0
placeholder_files=0

# 查找所有 Markdown 文件
find . -type f -name "*.md" | while read -r file; do
    total_files=$((total_files + 1))
    
    # 检查文件大小（小于100行视为占位符）
    line_count=$(wc -l < "$file" 2>/dev/null || echo "0")
    
    # 检查是否包含占位符标记
    is_placeholder=false
    for pattern in "${PLACEHOLDER_PATTERNS[@]}"; do
        if grep -qi "$pattern" "$file" 2>/dev/null; then
            is_placeholder=true
            break
        fi
    done
    
    # 如果文件很小或包含占位符标记
    if [ "$line_count" -lt 100 ] || [ "$is_placeholder" = true ]; then
        placeholder_files=$((placeholder_files + 1))
        
        # 检查文件开头是否已有标记
        if ! head -n 5 "$file" 2>/dev/null | grep -q "⚠️.*待完善"; then
            # 创建临时文件
            temp_file=$(mktemp)
            
            # 添加标记到文件开头
            echo "> $MARKER - 此文件为占位符，内容待完善" > "$temp_file"
            echo "> **最后更新**: $(date +%Y-%m-%d)" >> "$temp_file"
            echo "> **预期完成**: 待定" >> "$temp_file"
            echo "" >> "$temp_file"
            echo "---" >> "$temp_file"
            echo "" >> "$temp_file"
            
            # 追加原文件内容
            cat "$file" >> "$temp_file"
            
            # 替换原文件
            mv "$temp_file" "$file"
            
            marked_files=$((marked_files + 1))
            echo "  ✅ 已标记: $file ($line_count 行)"
        else
            echo "  ℹ️  已标记: $file"
        fi
    fi
done

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 统计结果:"
echo "  总文件数: $total_files"
echo "  占位符文件: $placeholder_files"
echo "  新标记文件: $marked_files"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "✅ 占位符标注完成！"

