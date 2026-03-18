# 脚本工具

> **项目**: Rust系统化学习项目
> **维护者**: Rust学习项目团队
> **最后更新**: 2026-03-18

---

## 脚本列表

### 🔧 归档管理

| 脚本 | 功能 | 使用场景 |
|------|------|----------|
| [archive_deprecated_content.py](archive_deprecated_content.py) | 归档过时内容 | 清理不再维护的文档 |
| [archive_root_status_reports.ps1](archive_root_status_reports.ps1) | 归档根目录状态报告 | 整理项目报告 |

### 📋 批量处理

| 脚本 | 功能 | 使用场景 |
|------|------|----------|
| [batch_update_all_historical_files.sh](batch_update_all_historical_files.sh) | 批量更新历史文件 | 版本升级时 |
| [batch_update_historical_files.ps1](batch_update_historical_files.ps1) | 批量更新（PowerShell） | Windows环境 |
| [migrate_versioned_files.ps1](migrate_versioned_files.ps1) | 迁移版本化文件 | 版本迁移 |

### ✅ 质量检查

| 脚本 | 功能 | 使用场景 |
|------|------|----------|
| [check_content_quality.ps1](check_content_quality.ps1) | 检查内容质量 | 内容审查 |
| [check_content_quality_simple.ps1](check_content_quality_simple.ps1) | 简化版质量检查 | 快速检查 |
| [check_docs_format.ps1](check_docs_format.ps1) | 检查文档格式 | 格式审查 |
| [check_docs_format_simple.ps1](check_docs_format_simple.ps1) | 简化版格式检查 | 快速检查 |

### 🔗 链接检查

| 脚本 | 功能 | 使用场景 |
|------|------|----------|
| [check_links.ps1](check_links.ps1) | 检查链接有效性 | CI/CD |
| [check_links.py](check_links.py) | Python版链接检查 | 跨平台 |
| [fix_anchor_links.py](fix_anchor_links.py) | 修复锚点链接 | 链接修复 |

### 📦 依赖检查

| 脚本 | 功能 | 使用场景 |
|------|------|----------|
| [check_dependencies.bat](check_dependencies.bat) | 检查依赖（Windows） | Windows环境 |
| [check_dependencies.sh](check_dependencies.sh) | 检查依赖（Linux/macOS） | Unix环境 |

### 🔧 配置修复

| 脚本 | 功能 | 使用场景 |
|------|------|----------|
| [fix_cargo_toml.py](fix_cargo_toml.py) | 修复Cargo.toml | 配置更新 |
| [fix_ci_version.py](fix_ci_version.py) | 修复CI版本 | CI/CD更新 |
| [fix_example_names.py](fix_example_names.py) | 修复示例命名 | 命名规范化 |

### 📊 版本跟踪

| 脚本 | 功能 | 使用场景 |
|------|------|----------|
| [rust_version_tracker.py](rust_version_tracker.py) | Rust版本跟踪 | 版本监控 |
| [update_historical_version_files.md](update_historical_version_files.md) | 版本文件更新指南 | 文档 |

### 📝 日常检查

| 脚本 | 功能 | 使用场景 |
|------|------|----------|
| [daily_checklist.ps1](daily_checklist.ps1) | 每日检查清单 | 日常维护 |
| [daily_checklist.sh](daily_checklist.sh) | 每日检查清单（Shell） | Unix环境 |

### 🧪 测试运行

| 脚本 | 功能 | 使用场景 |
|------|------|----------|
| [run_workspace_tests.ps1](run_workspace_tests.ps1) | 运行工作区测试 | 测试执行 |

---

## 使用示例

### 检查链接

```powershell
# Windows
.\scripts\check_links.ps1

# 或使用Python（跨平台）
python scripts/check_links.py
```

### 归档过时内容

```powershell
# 预览模式
python scripts/archive_deprecated_content.py --dry-run

# 执行归档
python scripts/archive_deprecated_content.py
```

### 检查内容质量

```powershell
.\scripts\check_content_quality.ps1
```

---

## 添加新脚本

如需添加新脚本，请遵循以下规范：

1. **命名规范**:
   - 使用`snake_case`或`kebab-case`
   - 脚本名称应清晰描述功能
   - 添加适当的文件扩展名

2. **文档要求**:
   - 脚本头部添加注释说明功能
   - 复杂脚本添加使用示例
   - 更新此README

3. **权限设置**:
   - Shell脚本: `chmod +x script.sh`
   - Python脚本: 添加shebang `#!/usr/bin/env python3`

---

## 维护说明

- 定期审查脚本有效性
- 删除不再使用的脚本
- 更新脚本以适配新版本的Rust/工具链

---

[返回项目主页](../README.md)
