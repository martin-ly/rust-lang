#!/bin/bash

# ================================================================
# 文档归档脚本 - Rust Learning System
# ================================================================
# 用途: 清理和归档 docs/docs/ 目录中的历史文档
# 日期: 2025-10-30
# 作者: AI Assistant
# ================================================================

set -e  # 遇到错误立即退出

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# 基础目录
BASE_DIR="docs/docs"
ARCHIVE_DIR="${BASE_DIR}/archive"
BACKUP_DIR="docs/backup"

echo -e "${BLUE}╔════════════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║  Rust Learning System - 文档归档工具          ║${NC}"
echo -e "${BLUE}╚════════════════════════════════════════════════╝${NC}"
echo ""

# ================================================================
# 函数: 创建目录结构
# ================================================================
create_directories() {
    echo -e "${YELLOW}📁 创建归档目录结构...${NC}"
    
    mkdir -p "${ARCHIVE_DIR}/phase_reports"
    mkdir -p "${ARCHIVE_DIR}/module_reports"
    mkdir -p "${ARCHIVE_DIR}/planning"
    mkdir -p "${ARCHIVE_DIR}/temp"
    mkdir -p "${ARCHIVE_DIR}/language_restructure"
    mkdir -p "${BACKUP_DIR}"
    
    echo -e "${GREEN}✅ 目录结构创建完成${NC}"
    echo ""
}

# ================================================================
# 函数: 创建备份
# ================================================================
create_backup() {
    echo -e "${YELLOW}💾 创建完整备份...${NC}"
    
    BACKUP_FILE="docs_backup_$(date +%Y%m%d_%H%M%S).tar.gz"
    tar -czf "${BACKUP_FILE}" docs/ 2>/dev/null || {
        echo -e "${RED}❌ 备份创建失败${NC}"
        exit 1
    }
    
    echo -e "${GREEN}✅ 备份创建成功: ${BACKUP_FILE}${NC}"
    echo -e "${BLUE}   大小: $(du -h ${BACKUP_FILE} | cut -f1)${NC}"
    echo ""
}

# ================================================================
# 函数: 归档阶段报告
# ================================================================
archive_phase_reports() {
    echo -e "${YELLOW}📦 归档阶段报告...${NC}"
    
    local count=0
    
    # 归档所有 PHASE 开头的文件
    for file in ${BASE_DIR}/PHASE*.md; do
        if [ -f "$file" ]; then
            mv "$file" "${ARCHIVE_DIR}/phase_reports/"
            ((count++))
            echo -e "${GREEN}  ✓ $(basename $file)${NC}"
        fi
    done
    
    echo -e "${BLUE}📊 归档了 ${count} 个阶段报告${NC}"
    echo ""
}

# ================================================================
# 函数: 归档模块报告
# ================================================================
archive_module_reports() {
    echo -e "${YELLOW}📦 归档模块报告...${NC}"
    
    local count=0
    
    # 归档 C02-C14 的详细报告（保留最新的总结）
    for file in ${BASE_DIR}/C0[2-9]_*.md ${BASE_DIR}/C1[0-4]_*.md; do
        if [ -f "$file" ]; then
            # 排除最新的完成总结
            if [[ ! "$file" =~ "2025_10_30" ]] && [[ ! "$file" =~ "COMPLETION_2025_10_25" ]]; then
                mv "$file" "${ARCHIVE_DIR}/module_reports/"
                ((count++))
                echo -e "${GREEN}  ✓ $(basename $file)${NC}"
            fi
        fi
    done
    
    echo -e "${BLUE}📊 归档了 ${count} 个模块报告${NC}"
    echo ""
}

# ================================================================
# 函数: 归档计划和状态文档
# ================================================================
archive_planning_docs() {
    echo -e "${YELLOW}📦 归档计划和状态文档...${NC}"
    
    local count=0
    
    # 归档计划文档
    for pattern in "PLAN" "STATUS" "STRATEGY" "ANALYSIS" "OUTLINE"; do
        for file in ${BASE_DIR}/*${pattern}*.md; do
            if [ -f "$file" ]; then
                # 排除最新的重要文档
                if [[ ! "$file" =~ "REMAINING_WORK" ]] && [[ ! "$file" =~ "2025_10_30" ]]; then
                    mv "$file" "${ARCHIVE_DIR}/planning/"
                    ((count++))
                    echo -e "${GREEN}  ✓ $(basename $file)${NC}"
                fi
            fi
        done
    done
    
    echo -e "${BLUE}📊 归档了 ${count} 个计划文档${NC}"
    echo ""
}

# ================================================================
# 函数: 归档临时文档
# ================================================================
archive_temp_docs() {
    echo -e "${YELLOW}📦 归档临时文档...${NC}"
    
    local count=0
    
    # 归档临时任务文档
    for pattern in "TASK" "LINK" "TOC" "FIX" "FALSE"; do
        for file in ${BASE_DIR}/*${pattern}*.md; do
            if [ -f "$file" ]; then
                mv "$file" "${ARCHIVE_DIR}/temp/"
                ((count++))
                echo -e "${GREEN}  ✓ $(basename $file)${NC}"
            fi
        done
    done
    
    echo -e "${BLUE}📊 归档了 ${count} 个临时文档${NC}"
    echo ""
}

# ================================================================
# 函数: 移动压缩包
# ================================================================
move_archives() {
    echo -e "${YELLOW}📦 移动压缩包文件...${NC}"
    
    local count=0
    
    # 移动所有 .rar 文件
    for file in ${BASE_DIR}/*.rar docs/swap/*.rar; do
        if [ -f "$file" ]; then
            mv "$file" "${BACKUP_DIR}/"
            ((count++))
            echo -e "${GREEN}  ✓ $(basename $file)${NC}"
        fi
    done
    
    echo -e "${BLUE}📊 移动了 ${count} 个压缩包${NC}"
    echo ""
}

# ================================================================
# 函数: 归档 language 子目录
# ================================================================
archive_language_dir() {
    echo -e "${YELLOW}📦 归档 language 子目录...${NC}"
    
    if [ -d "${BASE_DIR}/language/RESTRUCTURE_WORKING" ]; then
        mv ${BASE_DIR}/language/RESTRUCTURE_WORKING/* "${ARCHIVE_DIR}/language_restructure/" 2>/dev/null || true
        echo -e "${GREEN}✅ language/RESTRUCTURE_WORKING 内容已归档${NC}"
    fi
    
    echo ""
}

# ================================================================
# 函数: 生成归档报告
# ================================================================
generate_report() {
    echo -e "${YELLOW}📊 生成归档报告...${NC}"
    
    REPORT_FILE="${ARCHIVE_DIR}/ARCHIVE_INDEX.md"
    
    cat > "${REPORT_FILE}" << 'EOF'
# 归档文档索引

> **归档日期**: $(date +%Y-%m-%d)  
> **归档工具**: archive_docs.sh  
> **归档版本**: v1.0

---

## 📁 目录结构

```
archive/
├── phase_reports/           # 阶段报告 (PHASE*.md)
├── module_reports/          # 模块报告 (C02-C14 详细报告)
├── planning/                # 计划和状态文档
├── temp/                    # 临时工作文档
└── language_restructure/    # 语言重构报告
```

---

## 📊 归档统计

EOF
    
    echo "### 阶段报告" >> "${REPORT_FILE}"
    echo "文件数: $(ls -1 ${ARCHIVE_DIR}/phase_reports/*.md 2>/dev/null | wc -l)" >> "${REPORT_FILE}"
    echo "" >> "${REPORT_FILE}"
    
    echo "### 模块报告" >> "${REPORT_FILE}"
    echo "文件数: $(ls -1 ${ARCHIVE_DIR}/module_reports/*.md 2>/dev/null | wc -l)" >> "${REPORT_FILE}"
    echo "" >> "${REPORT_FILE}"
    
    echo "### 计划文档" >> "${REPORT_FILE}"
    echo "文件数: $(ls -1 ${ARCHIVE_DIR}/planning/*.md 2>/dev/null | wc -l)" >> "${REPORT_FILE}"
    echo "" >> "${REPORT_FILE}"
    
    echo "### 临时文档" >> "${REPORT_FILE}"
    echo "文件数: $(ls -1 ${ARCHIVE_DIR}/temp/*.md 2>/dev/null | wc -l)" >> "${REPORT_FILE}"
    echo "" >> "${REPORT_FILE}"
    
    echo -e "${GREEN}✅ 归档报告已生成: ${REPORT_FILE}${NC}"
    echo ""
}

# ================================================================
# 函数: 显示保留的核心文档
# ================================================================
show_remaining_docs() {
    echo -e "${YELLOW}📋 保留的核心文档列表:${NC}"
    echo ""
    
    ls -1 ${BASE_DIR}/*.md 2>/dev/null | while read file; do
        echo -e "${GREEN}  ✓ $(basename $file)${NC}"
    done
    
    echo ""
    echo -e "${BLUE}📊 核心文档数量: $(ls -1 ${BASE_DIR}/*.md 2>/dev/null | wc -l)${NC}"
    echo ""
}

# ================================================================
# 函数: 显示统计信息
# ================================================================
show_statistics() {
    echo -e "${BLUE}╔════════════════════════════════════════════════╗${NC}"
    echo -e "${BLUE}║  归档完成统计                                  ║${NC}"
    echo -e "${BLUE}╚════════════════════════════════════════════════╝${NC}"
    echo ""
    
    echo -e "${YELLOW}📁 归档文件统计:${NC}"
    echo -e "  阶段报告: $(ls -1 ${ARCHIVE_DIR}/phase_reports/*.md 2>/dev/null | wc -l) 个"
    echo -e "  模块报告: $(ls -1 ${ARCHIVE_DIR}/module_reports/*.md 2>/dev/null | wc -l) 个"
    echo -e "  计划文档: $(ls -1 ${ARCHIVE_DIR}/planning/*.md 2>/dev/null | wc -l) 个"
    echo -e "  临时文档: $(ls -1 ${ARCHIVE_DIR}/temp/*.md 2>/dev/null | wc -l) 个"
    echo -e "  备份文件: $(ls -1 ${BACKUP_DIR}/*.rar 2>/dev/null | wc -l) 个"
    echo ""
    
    echo -e "${YELLOW}📊 核心文档:${NC}"
    echo -e "  保留文档: $(ls -1 ${BASE_DIR}/*.md 2>/dev/null | wc -l) 个"
    echo ""
    
    echo -e "${GREEN}✅ 文档结构优化完成！${NC}"
    echo ""
}

# ================================================================
# 主函数
# ================================================================
main() {
    echo -e "${YELLOW}⚠️  即将开始归档操作，建议先备份！${NC}"
    echo -e "${YELLOW}   是否继续？ (y/n)${NC}"
    read -r answer
    
    if [[ ! "$answer" =~ ^[Yy]$ ]]; then
        echo -e "${RED}❌ 操作已取消${NC}"
        exit 0
    fi
    
    echo ""
    echo -e "${GREEN}🚀 开始归档流程...${NC}"
    echo ""
    
    # 执行归档步骤
    create_backup
    create_directories
    archive_phase_reports
    archive_module_reports
    archive_planning_docs
    archive_temp_docs
    move_archives
    archive_language_dir
    generate_report
    show_remaining_docs
    show_statistics
    
    echo -e "${GREEN}╔════════════════════════════════════════════════╗${NC}"
    echo -e "${GREEN}║  🎉 归档流程完成！                            ║${NC}"
    echo -e "${GREEN}╚════════════════════════════════════════════════╝${NC}"
    echo ""
    echo -e "${BLUE}📁 归档位置: ${ARCHIVE_DIR}${NC}"
    echo -e "${BLUE}💾 备份文件: $(ls -t docs_backup_*.tar.gz 2>/dev/null | head -1)${NC}"
    echo -e "${BLUE}📋 归档索引: ${ARCHIVE_DIR}/ARCHIVE_INDEX.md${NC}"
    echo ""
    echo -e "${YELLOW}💡 建议: 检查归档结果后，可以安全删除 swap 目录${NC}"
    echo ""
}

# 执行主函数
main

