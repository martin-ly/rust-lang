#!/bin/bash
# Rust 知识库快速搜索工具
# 用法: ./tools/knowledge_search.sh "关键词"

if [ -z "$1" ]; then
    echo "用法: $0 <搜索关键词>"
    echo "示例: $0 ownership"
    exit 1
fi

SEARCH_TERM="$1"
PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

echo "🔍 搜索 Rust 知识库: $SEARCH_TERM"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# 1. 搜索文档标题
echo ""
echo "📚 相关文档:"
find "$PROJECT_ROOT" -name "*.md" -type f \
    -not -path "*/node_modules/*" \
    -not -path "*/.git/*" \
    -not -path "*/archive/*" | \
while read file; do
    title=$(head -1 "$file" 2>/dev/null | sed 's/^#* //')
    if echo "$title $file" | grep -i "$SEARCH_TERM" > /dev/null 2>&1; then
        rel_path=$(echo "$file" | sed "s|$PROJECT_ROOT/||")
        echo "  📄 $rel_path"
        echo "     $title"
    fi
done | head -15

# 2. 搜索文档内容
echo ""
echo "📖 内容匹配 (前 10 条):"
grep -r -i -n --include="*.md" \
    --exclude-dir=node_modules \
    --exclude-dir=.git \
    --exclude-dir=archive \
    "$SEARCH_TERM" "$PROJECT_ROOT" 2>/dev/null | \
sed "s|$PROJECT_ROOT/||" | \
head -10

# 3. 搜索代码示例
echo ""
echo "💻 代码示例 (前 10 条):"
grep -r -i -n --include="*.rs" \
    --exclude-dir=target \
    --exclude-dir=node_modules \
    "$SEARCH_TERM" "$PROJECT_ROOT" 2>/dev/null | \
sed "s|$PROJECT_ROOT/||" | \
head -10

# 4. 统计
echo ""
echo "📊 搜索统计:"
doc_count=$(grep -r -i -l --include="*.md" --exclude-dir=archive "$SEARCH_TERM" "$PROJECT_ROOT" 2>/dev/null | wc -l)
code_count=$(grep -r -i -l --include="*.rs" "$SEARCH_TERM" "$PROJECT_ROOT" 2>/dev/null | wc -l)
echo "  - 相关文档: $doc_count 个"
echo "  - 相关代码: $code_count 个"

echo ""
echo "✅ 搜索完成"

