# 文档格式快速检查清单
>
> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **归档日期**: 2026-02-20
> **归档原因**: 过程性文档归档
> **状态**: 📦 已归档

---


> **用途**: 快速检查 Markdown 文档格式合规性
> **适用**: 所有 docs 目录下的 .md 文件

---

## ✅ 元信息检查（所有文档必需）

- [ ] 包含 `> **创建日期**: YYYY-MM-DD`
- [ ] 包含 `> **最后更新**: YYYY-MM-DD`
- [ ] 包含 `> **Rust 版本**: 1.93.1+ (Edition 2024)`
- [ ] 包含 `> **状态**: ✅ 已完成 / 🔄 进行中 / 📋 规划中`
- [ ] 日期格式为 `YYYY-MM-DD`（非 `YYYY/MM/DD` 或其他）
- [ ] key 与冒号间无空格 (`**创建日期**:` 非 `**创建日期** :`)
- [ ] 冒号后有一空格 (`: 2026` 非 `:2026`)

---

## ✅ 标题层级检查

- [ ] 一级标题 `#` **不含 emoji**
- [ ] 二级标题 `##` 可选 emoji，但同类文档统一
- [ ] 目录块标题统一为 `## 📊 目录`
- [ ] 标题层级不跳跃（无 `#` → `###` 跳过 `##`）

---

## ✅ 表格格式检查

- [ ] 分隔行使用 `| :--- | :--- | :--- |`（左对齐）
- [ ] 不使用 `|---|` 或 `| :---: |`（居中对齐）
- [ ] 每行列数相同
- [ ] 表格前后有空行

**正确示例**:

```markdown
| 列 A | 列 B | 列 C |
| :--- | :--- | :--- |
| 内容 | 内容 | 内容 |
```

**错误示例**:

```markdown
| 列 A | 列 B | 列 C |
| :--- | :--- | :--- |
| 内容 | 内容 |
```

---

## ✅ 链接格式检查

- [ ] 使用相对路径 `./path` 或 `../path`
- [ ] 不使用绝对路径 `/docs/path`
- [ ] 格式为 `[文本](路径)`
- [ ] 链接指向的文件存在

---

## ✅ 中文格式检查

- [ ] 术语使用一致（不混用 `泛型` / `generics`）
- [ ] 中文标点使用正确（，`。` 非 `,` `.`）

---

## ✅ 文末元信息（核心研究笔记必需）

适用于: formal_methods/, type_theory/, software_design_theory/, experiments/

- [ ] 文末包含 `---` 分隔线
- [ ] 包含 `**维护者**: 团队名称`
- [ ] 包含 `**最后更新**: YYYY-MM-DD`
- [ ] 包含 `**状态**: ✅ 已完成`

**正确示例**:

```markdown
---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-20
**状态**: ✅ 已完成
```

---

## 🔧 常用修复命令

### PowerShell 批量检查

```powershell
# 检查所有 .md 文件
Get-ChildItem -Path docs -Recurse -Filter "*.md" | ForEach-Object {
    Write-Host "检查: $($_.FullName)"
    # 检查元信息
    $content = Get-Content $_.FullName -Raw
    if ($content -notmatch "\*\*Rust 版本\*\*:") {
        Write-Host "  ⚠️ 缺少 Rust 版本" -ForegroundColor Yellow
    }
    if ($content -notmatch "\*\*创建日期\*\*:") {
        Write-Host "  ⚠️ 缺少创建日期" -ForegroundColor Yellow
    }
}
```

---

## 🦀 Rust 配置检查示例

以下是一个简单的 Rust 程序，用于检查文档元信息格式合规性：

```rust
//! 文档元信息格式检查工具
//! 用法: cargo run --bin doc_format_checker -- <docs_path>

use std::fs;
use std::path::Path;

/// 文档元信息结构
#[derive(Debug)]
struct DocMeta {
    created_date: Option<String>,
    last_updated: Option<String>,
    rust_version: Option<String>,
    status: Option<String>,
}

impl DocMeta {
    fn parse_from_content(content: &str) -> Self {
        let mut meta = DocMeta {
            created_date: None,
            last_updated: None,
            rust_version: None,
            status: None,
        };

        for line in content.lines() {
            if line.contains("**创建日期**:") {
                meta.created_date = extract_value(line);
            } else if line.contains("**最后更新**:") {
                meta.last_updated = extract_value(line);
            } else if line.contains("**Rust 版本**:") {
                meta.rust_version = extract_value(line);
            } else if line.contains("**状态**:") {
                meta.status = extract_value(line);
            }
        }

        meta
    }

    fn is_complete(&self) -> bool {
        self.created_date.is_some()
            && self.last_updated.is_some()
            && self.rust_version.is_some()
            && self.status.is_some()
    }
}

fn extract_value(line: &str) -> Option<String> {
    line.split(':').nth(1).map(|s| s.trim().to_string())
}

fn check_docs_format(docs_path: &str) -> Result<(), Box<dyn std::error::Error>> {
    let mut total = 0;
    let mut incomplete = 0;

    for entry in fs::read_dir(docs_path)? {
        let entry = entry?;
        let path = entry.path();

        if path.extension().map_or(false, |e| e == "md") {
            total += 1;
            let content = fs::read_to_string(&path)?;
            let meta = DocMeta::parse_from_content(&content);

            if !meta.is_complete() {
                incomplete += 1;
                println!("⚠️  {} 格式不完整", path.display());
            }
        }
    }

    println!("\n========== 检查完成 ==========");
    println!("总文件数: {}", total);
    println!("格式完整: {}", total - incomplete);
    println!("格式不完整: {}", incomplete);

    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let docs_path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "docs".to_string());

    println!("📋 检查文档格式: {}", docs_path);
    check_docs_format(&docs_path)
}
```

---

## 📖 相关文档

- [DOCS_STRUCTURE_AND_FORMAT_AUDIT_REPORT](./DOCS_STRUCTURE_AND_FORMAT_AUDIT_REPORT.md) - 完整审计报告
- [QUALITY_CHECKLIST](../../../research_notes/QUALITY_CHECKLIST.md) - 质量检查清单
- [FORMAT_AND_CONTENT_ALIGNMENT_PLAN](./FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md) - 格式统一与内容对齐计划
- [FORMAT_FIX_COMPLETION_REPORT](./FORMAT_FIX_COMPLETION_REPORT.md) - 格式修复完成报告
- [FORMAT_FIX_FINAL_REPORT](./FORMAT_FIX_FINAL_REPORT.md) - 格式修复最终报告
- [FORMAT_FIX_PROGRESS_REPORT](./FORMAT_FIX_PROGRESS_REPORT.md) - 格式修复进度报告
- [REFACTORING_COMPLETION_2026_02](./REFACTORING_COMPLETION_2026_02.md) - 重构完成报告
- [RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN](./RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md) - 研究笔记批判分析与改进计划
