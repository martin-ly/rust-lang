#!/bin/bash
# 项目统计生成脚本

echo "======================================"
echo "Rust 学习项目统计"
echo "======================================"
echo ""

# 统计代码行数
echo "📊 代码统计:"
echo "  Rust 代码行数:"
find crates -name "*.rs" -type f -exec wc -l {} + | tail -1
echo ""

# 统计文档行数
echo "  Markdown 文档行数:"
find . -name "*.md" -type f -not -path "./archive/*" -exec wc -l {} + | tail -1
echo ""

# 统计文件数量
echo "📁 文件统计:"
echo "  Rust 源文件: $(find crates -name "*.rs" -type f | wc -l)"
echo "  Markdown 文档: $(find . -name "*.md" -type f -not -path "./archive/*" | wc -l)"
echo "  示例文件: $(find examples -name "*.rs" -type f 2>/dev/null | wc -l)"
echo ""

# 统计测试
echo "🧪 测试统计:"
cargo test --workspace --no-run 2>/dev/null | grep -E "test result|Compiling" || echo "  需要编译测试"
echo ""

# 检查编译状态
echo "🔨 编译状态:"
cargo check --workspace 2>&1 | grep -E "Finished|error" | head -1
echo ""

echo "======================================"
