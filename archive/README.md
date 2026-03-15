# 归档目录说明

> 项目维护过程中产生的临时文件归档

---

## 📁 目录结构

```text
archive/
├── completion_certificates/    # 完成证书类文件
│   └── 项目各阶段的完成声明和证书
│
├── progress_tracking/          # 进度跟踪类文件
│   └── 项目开发过程中的进度报告
│
├── project_reports/            # 项目报告类文件
│   └── 综合分析报告和规划文档
│
├── project_scripts/            # 维护脚本
│   └── 项目维护过程中使用的脚本
│
├── project_logs/               # 日志文件
│   └── 各种检查和构建日志
│
├── verification_reports/       # 验证报告
│   └── 交叉引用验证和审计报告
│
├── deprecated/                 # 已废弃内容
│   └── 不再使用的旧版本内容
│
├── process_reports/            # 过程报告
│   └── 开发过程中的中间报告
│
├── temp/                       # 临时文件
│   └── 临时生成的文件
│
└── reports/                    # 早期报告
    └── 项目初期的分析报告
```

---

## 📝 归档说明

### 为什么要归档？

1. **保持项目整洁**: 根目录只保留核心文件
2. **历史记录**: 保留项目发展历程
3. **可追溯**: 需要时可查阅历史文档
4. **避免干扰**: 学习者不会被大量报告文件分散注意力

### 哪些文件被归档？

| 类别 | 示例 | 原因 |
|------|------|------|
| 完成证书 | 100_PERCENT_*.md | 项目完成声明，非学习必需 |
| 进度报告 | PROGRESS_*.md | 开发过程跟踪 |
| 验证报告 | VERIFICATION_*.md | 质量保证文档 |
| 维护脚本 | fix_*.py, check_*.py | 临时维护工具 |
| 日志文件 | *.log,*.txt | 构建和检查日志 |

### 哪些文件保留？

| 类别 | 示例 | 原因 |
|------|------|------|
| 核心文档 | README.md, FAQ.md | 项目入口和指南 |
| 学习文档 | LEARNING_CHECKLIST.md | 学习必需 |
| 架构文档 | PROJECT_STRUCTURE.md | 项目结构说明 |
| 核心配置 | Cargo.toml, deny.toml | 项目配置 |
| 工具脚本 | tools/*.py | 有用的工具脚本 |

---

## 🔍 如何查阅归档文件？

如需查阅历史文档，可按以下方式：

```bash
# 查看完成证书
ls archive/completion_certificates/

# 查看进度报告
ls archive/progress_tracking/

# 搜索特定文件
find archive/ -name "*2026_03*"
```

---

## 📊 归档统计

| 目录 | 文件数 | 说明 |
|------|--------|------|
| completion_certificates | 20+ | 完成声明和证书 |
| progress_tracking | 30+ | 进度报告 |
| project_reports | 15+ | 项目报告 |
| project_scripts | 20+ | 维护脚本 |
| project_logs | 10+ | 日志文件 |
| verification_reports | 10+ | 验证报告 |

---

**注意**: 归档文件仅供参考，项目最新状态以根目录文档为准。

---

*最后更新: 2026-03-15*:
