#!/bin/bash
# 改进的链接检查脚本
# 用法: ./check_links.sh

set -e

FORMAL_SYSTEM_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$FORMAL_SYSTEM_DIR/../.." && pwd)"

echo "🔍 检查形式化系统链接..."
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

cd "$FORMAL_SYSTEM_DIR"

# 统计计数器
total_links=0
broken_links=0
valid_links=0

# 临时文件存储结果
broken_file=$(mktemp)
valid_file=$(mktemp)

# 查找所有 Markdown 文件中的链接
find . -type f -name "*.md" | while read -r file; do
    # 提取所有相对路径链接
    grep -oE '\[([^\]]+)\]\(([^)]+)\)' "$file" 2>/dev/null | \
    while IFS= read -r match; do
        # 提取链接部分
        link=$(echo "$match" | sed -E 's/\[([^\]]+)\]\(([^)]+)\)/\2/')
        
        # 跳过空链接、锚点链接、外部链接
        if [[ -z "$link" ]] || [[ "$link" =~ ^# ]] || [[ "$link" =~ ^https?:// ]] || [[ "$link" =~ ^mailto: ]]; then
            continue
        fi
        
        # 只处理相对路径链接
        if [[ "$link" =~ ^\.\.?/ ]] || [[ ! "$link" =~ ^/ ]]; then
            total_links=$((total_links + 1))
            
            # 计算目标文件路径
            file_dir=$(dirname "$file")
            
            # 如果是相对路径，转换为绝对路径
            if [[ "$link" =~ ^\.\./ ]]; then
                # 向上路径
                target_path="$FORMAL_SYSTEM_DIR/$file_dir/$link"
            elif [[ "$link" =~ ^\./ ]]; then
                # 当前目录
                target_path="$FORMAL_SYSTEM_DIR/$file_dir/${link#./}"
            else
                # 相对路径
                target_path="$FORMAL_SYSTEM_DIR/$file_dir/$link"
            fi
            
            # 规范化路径
            target_path=$(cd "$(dirname "$target_path")" 2>/dev/null && pwd)/$(basename "$target_path") 2>/dev/null || echo "$target_path"
            
            # 移除末尾的锚点
            target_path="${target_path%%#*}"
            
            # 检查链接是否有效
            if [ -f "$target_path" ] || [ -d "$target_path" ]; then
                valid_links=$((valid_links + 1))
                echo "  ✅ $file -> $link" >> "$valid_file"
            else
                broken_links=$((broken_links + 1))
                echo "  ❌ $file -> $link" >> "$broken_file"
            fi
        fi
    done
done

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 链接检查结果:"
echo "  总链接数: $total_links"
echo "  有效链接: $valid_links"
echo "  无效链接: $broken_links"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# 如果找到无效链接，显示前10个
if [ -s "$broken_file" ]; then
    echo "❌ 发现 $broken_links 个无效链接（显示前10个）:"
    echo ""
    head -10 "$broken_file"
    echo ""
    echo "⚠️  请修复这些链接！查看完整列表: cat $broken_file"
    exit 1
else
    echo "✅ 所有链接有效！"
    exit 0
fi

# 清理临时文件
rm -f "$broken_file" "$valid_file"
