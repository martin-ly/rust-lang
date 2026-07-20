#!/bin/bash
# 交叉引用验证和更新工具
# 用法: ./verify_cross_references.sh

set -e

FORMAL_SYSTEM_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$FORMAL_SYSTEM_DIR/../.." && pwd)"

echo "🔗 验证和更新交叉引用..."
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

cd "$FORMAL_SYSTEM_DIR"

# 模块映射表
declare -A MODULE_MAP
MODULE_MAP["01_theoretical_foundations/01_type_system"]="crates/c02_type_system"
MODULE_MAP["01_theoretical_foundations/03_ownership_borrowing"]="crates/c01_ownership_borrow_scope"
MODULE_MAP["01_theoretical_foundations/04_concurrency_models"]="crates/c05_threads"
MODULE_MAP["01_theoretical_foundations/08_macro_system"]="crates/c11_macro_system"
MODULE_MAP["02_programming_paradigms/02_async"]="crates/c06_async"
MODULE_MAP["03_design_patterns"]="crates/c09_design_pattern"

# 统计计数器
total_files=0
updated_files=0
skipped_files=0

# 查找所有交叉引用清单文件
find . -type f -name "*交叉引用清单.md" -o -name "*cross_reference*.md" | while read -r file; do
    total_files=$((total_files + 1))
    
    # 获取模块路径
    module_path=$(dirname "$file" | sed 's|^\./||')
    
    # 检查是否有对应的主项目模块
    if [[ -n "${MODULE_MAP[$module_path]}" ]]; then
        crate_path="${MODULE_MAP[$module_path]}"
        crate_relative_path="../../../../$crate_path"
        
        # 检查文件是否已包含主项目链接
        if ! grep -q "## 💻 实际代码示例\|## 实际代码示例\|主项目模块\|C01\|C02\|C06\|C09\|C11" "$file" 2>/dev/null; then
            # 在文件末尾添加实际代码示例部分
            {
                echo ""
                echo "---"
                echo ""
                echo "## 💻 实际代码示例"
                echo ""
                echo "将形式化理论知识应用到实际代码中："
                echo ""
                
                case "$module_path" in
                    "01_theoretical_foundations/01_type_system")
                        echo "- **[C02 类型系统模块]($crate_relative_path/README.md)** - 完整的类型系统学习模块"
                        echo "- **[代码示例]($crate_relative_path/examples/)** - 类型系统实际代码示例"
                        echo "- **[Tier 文档]($crate_relative_path/docs/)** - 4-Tier 分层学习文档"
                        ;;
                    "01_theoretical_foundations/03_ownership_borrowing")
                        echo "- **[C01 所有权模块]($crate_relative_path/README.md)** - 完整的所有权学习模块"
                        echo "- **[代码示例]($crate_relative_path/examples/)** - 150+ 个所有权示例"
                        echo "- **[综合示例]($crate_relative_path/examples/comprehensive_ownership_examples.rs)** - 完整的所有权应用"
                        ;;
                    "01_theoretical_foundations/04_concurrency_models")
                        echo "- **[C05 并发模块]($crate_relative_path/README.md)** - 完整的并发学习模块"
                        echo "- **[代码示例]($crate_relative_path/examples/)** - 并发实际代码示例"
                        ;;
                    "01_theoretical_foundations/08_macro_system")
                        echo "- **[C11 宏系统模块]($crate_relative_path/README.md)** - 完整的宏系统学习模块"
                        echo "- **[代码示例]($crate_relative_path/examples/)** - 宏系统实际代码示例"
                        ;;
                    "02_programming_paradigms/02_async")
                        echo "- **[C06 异步编程模块]($crate_relative_path/README.md)** - 完整的异步编程学习模块"
                        echo "- **[代码示例]($crate_relative_path/examples/)** - 460+ 个异步编程示例"
                        echo "- **[Reactor 模式实现]($crate_relative_path/src/reactor/)** - Reactor 模式完整实现"
                        ;;
                    "03_design_patterns")
                        echo "- **[C09 设计模式模块]($crate_relative_path/README.md)** - 完整的设计模式学习模块"
                        echo "- **[代码示例]($crate_relative_path/examples/)** - 150+ 个设计模式示例"
                        ;;
                esac
                
                echo ""
                echo "**学习路径**: 形式化理论 → 实际代码 → 验证理解"
                echo ""
                echo "---"
            } >> "$file"
            
            updated_files=$((updated_files + 1))
            echo "  ✅ 已更新: $file"
        else
            skipped_files=$((skipped_files + 1))
            echo "  ℹ️  已包含: $file"
        fi
    else
        skipped_files=$((skipped_files + 1))
        echo "  ⚠️  无映射: $file"
    fi
done

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 交叉引用更新结果:"
echo "  总文件数: $total_files"
echo "  已更新: $updated_files"
echo "  已跳过: $skipped_files"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "✅ 交叉引用验证完成！"

