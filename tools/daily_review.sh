#!/bin/bash
# Rust 知识库每日回顾工具
# 用法: ./tools/daily_review.sh

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

echo "📚 Rust 知识库 - 每日回顾"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "日期: $(date +%Y-%m-%d)"
echo ""

# 1. 随机复习概念
echo "🎲 今日随机复习 (3个概念):"
if [ -d "$PROJECT_ROOT/docs/quick_reference" ]; then
    find "$PROJECT_ROOT/docs/quick_reference" -name "*.md" 2>/dev/null | \
    shuf -n 3 | \
    while read file; do
        name=$(basename "$file" .md)
        echo "  ✅ $name"
    done
else
    echo "  ⚠️  quick_reference 目录尚未创建"
fi

# 2. 最近研究笔记
echo ""
echo "📝 最近研究笔记:"
if [ -d "$PROJECT_ROOT/docs/research_notes" ]; then
    find "$PROJECT_ROOT/docs/research_notes" -name "*.md" -type f 2>/dev/null | \
    xargs ls -lt 2>/dev/null | \
    head -5 | \
    while read line; do
        file=$(echo "$line" | awk '{print $NF}')
        if [ -f "$file" ]; then
            name=$(basename "$file" .md)
            date=$(echo "$line" | awk '{print $6,$7}')
            echo "  📄 $name ($date)"
        fi
    done
else
    echo "  ⚠️  research_notes 目录尚未创建"
fi

# 3. 知识库统计
echo ""
echo "📊 知识库统计:"
total_docs=$(find "$PROJECT_ROOT" -name "*.md" -type f -not -path "*/node_modules/*" -not -path "*/.git/*" 2>/dev/null | wc -l)
total_code=$(find "$PROJECT_ROOT" -name "*.rs" -type f -not -path "*/target/*" 2>/dev/null | wc -l)
research_notes=$(find "$PROJECT_ROOT/docs/research_notes" -name "*.md" -type f 2>/dev/null | wc -l)

echo "  - 总文档数: $total_docs 个"
echo "  - 代码示例: $total_code 个"
echo "  - 研究笔记: $research_notes 个"

# 4. 最近更新的模块
echo ""
echo "🔄 最近活跃模块:"
find "$PROJECT_ROOT/crates" -name "*.rs" -o -name "*.md" 2>/dev/null | \
xargs ls -lt 2>/dev/null | \
head -5 | \
while read line; do
    file=$(echo "$line" | awk '{print $NF}')
    if [ -f "$file" ]; then
        module=$(echo "$file" | sed "s|$PROJECT_ROOT/crates/||" | cut -d'/' -f1)
        date=$(echo "$line" | awk '{print $6,$7}')
        echo "  📦 $module ($date)"
    fi
done | sort -u

# 5. 建议
echo ""
echo "💡 今日建议:"
day_of_week=$(date +%u)
case $day_of_week in
    1) echo "  - 周一: 回顾上周研究笔记" ;;
    2) echo "  - 周二: 深入一个形式化主题" ;;
    3) echo "  - 周三: 补充代码示例" ;;
    4) echo "  - 周四: 优化文档结构" ;;
    5) echo "  - 周五: 总结本周收获" ;;
    6) echo "  - 周六: 自由研究时间" ;;
    7) echo "  - 周日: 规划下周学习" ;;
esac

echo ""
echo "🦀 开始今天的 Rust 探索吧！"


