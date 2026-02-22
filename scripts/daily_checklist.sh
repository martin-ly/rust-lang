#!/bin/bash
# 每日任务检查清单脚本
# 用法: ./scripts/daily_checklist.sh

echo "=================================="
echo "每日任务检查清单 - $(date +%Y-%m-%d)"
echo "=================================="
echo ""

# 检查Coq文件编译状态
echo "📋 1. Coq文件编译检查"
echo "----------------------"
if command -v coqc &> /dev/null; then
    cd docs/research_notes/coq_skeleton 2>/dev/null
    if [ $? -eq 0 ]; then
        for f in *.v; do
            if [ -f "$f" ]; then
                echo -n "  检查 $f: "
                if coqc -quiet "$f" 2>/dev/null; then
                    echo "✅ 编译通过"
                else
                    echo "❌ 编译失败"
                fi
            fi
        done
        cd - > /dev/null
    fi
else
    echo "  ⚠️  Coq未安装，跳过编译检查"
fi
echo ""

# 统计Admitted数量
echo "📋 2. Coq证明完成度统计"
echo "----------------------"
cd docs/research_notes/coq_skeleton 2>/dev/null
if [ $? -eq 0 ]; then
    for f in *.v; do
        if [ -f "$f" ]; then
            admitted_count=$(grep -c "Admitted" "$f" 2>/dev/null || echo 0)
            qed_count=$(grep -c "Qed" "$f" 2>/dev/null || echo 0)
            echo "  $f: Admitted=$admitted_count, Qed=$qed_count"
        fi
    done
    cd - > /dev/null
else
    echo "  ⚠️  未找到Coq文件"
fi
echo ""

# 检查Markdown文件格式
echo "📋 3. Markdown文件格式检查"
echo "----------------------"
# 检查表格格式
invalid_tables=$(grep -r "\|:\-" docs/research_notes --include="*.md" 2>/dev/null | grep -v "| :---" | wc -l)
if [ "$invalid_tables" -eq 0 ]; then
    echo "  ✅ 表格格式正确"
else
    echo "  ⚠️  发现 $invalid_tables 处表格格式问题"
fi
echo ""

# 统计文档数量
echo "📋 4. 文档资产统计"
echo "----------------------"
formal_methods_count=$(find docs/research_notes/formal_methods -name "*.md" 2>/dev/null | wc -l)
software_design_count=$(find docs/research_notes/software_design_theory -name "*.md" 2>/dev/null | wc -l)
type_theory_count=$(find docs/research_notes/type_theory -name "*.md" 2>/dev/null | wc -l)
coq_files_count=$(find docs/research_notes/coq_skeleton -name "*.v" 2>/dev/null | wc -l)

echo "  formal_methods文档: $formal_methods_count"
echo "  software_design_theory文档: $software_design_count"
echo "  type_theory文档: $type_theory_count"
echo "  Coq文件: $coq_files_count"
echo ""

# 检查本周任务进度
echo "📋 5. 本周任务检查"
echo "----------------------"
echo "  Week 1目标: OWNERSHIP_UNIQUENESS.v 编译通过，Admitted ≤ 5"
cd docs/research_notes/coq_skeleton 2>/dev/null
if [ -f "OWNERSHIP_UNIQUENESS.v" ]; then
    ow_admitted=$(grep -c "Admitted" "OWNERSHIP_UNIQUENESS.v" 2>/dev/null || echo 0)
    echo "  当前Admitted数量: $ow_admitted"
    if [ "$ow_admitted" -le 5 ]; then
        echo "  ✅ Week 1目标达成"
    else
        echo "  🔄 还需完成 $((ow_admitted - 5)) 个证明"
    fi
fi
cd - > /dev/null
echo ""

# Git状态检查
echo "📋 6. Git提交检查"
echo "----------------------"
if [ -d .git ]; then
    uncommitted=$(git status --porcelain 2>/dev/null | wc -l)
    if [ "$uncommitted" -eq 0 ]; then
        echo "  ✅ 所有更改已提交"
    else
        echo "  📝 有 $uncommitted 个未提交更改"
        git status --short
    fi
else
    echo "  ⚠️  非Git仓库"
fi
echo ""

echo "=================================="
echo "检查完成 - 继续推进100%完成!"
echo "=================================="
