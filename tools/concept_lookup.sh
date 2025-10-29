#!/bin/bash
# Rust 概念快速查找工具
# 用法: ./tools/concept_lookup.sh "概念名称"

if [ -z "$1" ]; then
    echo "用法: $0 <概念名称>"
    echo "示例: $0 lifetime"
    exit 1
fi

CONCEPT="$1"
PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

echo "🔍 查找概念: $CONCEPT"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# 1. 查找定义
echo ""
echo "📖 定义位置:"
grep -r -i -n "^## .*$CONCEPT" --include="*.md" \
    --exclude-dir=node_modules \
    --exclude-dir=.git \
    "$PROJECT_ROOT" 2>/dev/null | \
sed "s|$PROJECT_ROOT/||" | \
head -5

# 2. 查找代码示例
echo ""
echo "💻 代码示例:"
grep -r -i -l "$CONCEPT" --include="*.rs" \
    --exclude-dir=target \
    "$PROJECT_ROOT/crates" 2>/dev/null | \
sed "s|$PROJECT_ROOT/||" | \
head -5

# 3. 查找相关文档
echo ""
echo "📚 相关文档:"
grep -r -i -l "$CONCEPT" --include="*.md" \
    --exclude-dir=archive \
    "$PROJECT_ROOT/crates" 2>/dev/null | \
sed "s|$PROJECT_ROOT/||" | \
head -10

# 4. 查找相关概念 (通过链接)
echo ""
echo "🔗 相关概念:"
grep -r -i "$CONCEPT" --include="*.md" \
    "$PROJECT_ROOT" 2>/dev/null | \
grep -o "\[\w\+\]" | \
sed 's/\[//g; s/\]//g' | \
sort -u | \
grep -v "^$CONCEPT$" | \
head -10 | \
while read related; do
    echo "  - $related"
done

# 5. 快速参考
echo ""
echo "🚀 快速参考:"
if [ -f "$PROJECT_ROOT/docs/quick_reference/${CONCEPT}_cheatsheet.md" ]; then
    echo "  ✅ 找到快速参考: docs/quick_reference/${CONCEPT}_cheatsheet.md"
else
    echo "  💡 建议创建快速参考: docs/quick_reference/${CONCEPT}_cheatsheet.md"
fi

# 6. 研究笔记
echo ""
echo "📝 研究笔记:"
if [ -d "$PROJECT_ROOT/docs/research_notes" ]; then
    grep -r -i -l "$CONCEPT" --include="*.md" \
        "$PROJECT_ROOT/docs/research_notes" 2>/dev/null | \
    sed "s|$PROJECT_ROOT/||" | \
    while read note; do
        echo "  📄 $note"
    done
fi

echo ""
echo "✅ 查找完成"

