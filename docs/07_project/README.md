# 项目元文档

> **创建日期**: 2025-12-11
> **最后更新**: 2026-02-27
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 100% 完成
> **用途**: 知识结构、版本追踪、文档交叉引用；结构可维护、任务可追踪
> **判定目标**: 结构可维护、任务可追踪
> **完整结构**: [DOCS_STRUCTURE_OVERVIEW](../DOCS_STRUCTURE_OVERVIEW.md) § 2.6

## 代码示例

### 项目元文档索引生成器

```rust
//! 自动生成 07_project 目录文档索引
use std::collections::HashMap;
use std::fs;
use std::path::Path;

struct ProjectDocIndexer;

impl ProjectDocIndexer {
    fn scan_docs() -> Vec<DocInfo> {
        let mut docs = Vec::new();

        if let Ok(entries) = fs::read_dir("docs/07_project") {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().map_or(false, |e| e == "md") {
                    if let Some(info) = Self::parse_doc(&path) {
                        docs.push(info);
                    }
                }
            }
        }

        docs.sort_by(|a, b| a.name.cmp(&b.name));
        docs
    }

    fn parse_doc(path: &Path) -> Option<DocInfo> {
        let content = fs::read_to_string(path).ok()?;
        let filename = path.file_stem()?.to_string_lossy().to_string();

        // 解析标题（第一个 # 开头的行）
        let title = content.lines()
            .find(|l| l.starts_with("# "))
            .map(|l| l.trim_start_matches("# ").to_string())
            .unwrap_or_else(|| filename.clone());

        // 解析描述（从元数据中提取）
        let description = content.lines()
            .find(|l| l.contains("用途") || l.contains("目的"))
            .and_then(|l| l.split(':').nth(1))
            .map(|s| s.trim().to_string())
            .unwrap_or_else(|| "项目元文档".to_string());

        // 解析状态
        let status = content.lines()
            .find(|l| l.contains("状态"))
            .and_then(|l| {
                if l.contains("已完成") { Some("✅") }
                else if l.contains("进行中") { Some("🚧") }
                else { Some("📋") }
            })
            .unwrap_or("📋")
            .to_string();

        Some(DocInfo {
            name: filename,
            title,
            description,
            status,
        })
    }

    fn generate_readme(docs: &[DocInfo]) -> String {
        let mut output = String::from("# 项目元文档\n\n");
        output.push_str("> **用途**: 知识结构、版本追踪、文档交叉引用；结构可维护、任务可追踪\n\n"
        );
        output.push_str("## 文档列表\n\n");
        output.push_str("| 文档 | 说明 | 状态 |\n");
        output.push_str("| :--- | :--- | :--- |\n");

        for doc in docs {
            output.push_str(&format!(
                "| [{}](./{}.md) | {} | {} |\n",
                doc.title, doc.name, doc.description, doc.status
            ));
        }

        output.push_str("\n## 主索引\n\n");
        output.push_str("[00_MASTER_INDEX.md](../00_MASTER_INDEX.md)\n");

        output
    }
}

struct DocInfo {
    name: String,
    title: String,
    description: String,
    status: String,
}

fn main() {
    let docs = ProjectDocIndexer::scan_docs();
    let readme = ProjectDocIndexer::generate_readme(&docs);

    fs::write("docs/07_project/README.md", readme).unwrap();
    println!("README.md 已更新，包含 {} 个文档", docs.len());
}
```

---

## 形式化链接

### 研究笔记关联

- **综合总览**: [COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md](../research_notes/COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md) - 全局一致性、语义归纳、概念族谱
- **证明系统**: [FORMAL_PROOF_SYSTEM_GUIDE.md](../research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md) - 形式化证明系统指南
- **权威对齐**: [AUTHORITATIVE_ALIGNMENT_GUIDE.md](../research_notes/AUTHORITATIVE_ALIGNMENT_GUIDE.md) - 权威来源对齐指南

### 文档分类

| 类别 | 文档 | 说明 |
| :--- | :--- | :--- |
| **知识结构** | KNOWLEDGE_STRUCTURE_FRAMEWORK.md<br>MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md | 定义知识结构体系<br>模块知识结构补充指南 |
| **版本追踪** | [RUST_RELEASE_TRACKING_CHECKLIST.md](../archive/process_reports/2026_02/project/RUST_RELEASE_TRACKING_CHECKLIST.md) (归档)<br>版本追踪文档 | 新版本发布追踪流程<br>各模块适配状态 |
| **文档管理** | [DOCUMENTATION_CROSS_REFERENCE_GUIDE.md](./DOCUMENTATION_CROSS_REFERENCE_GUIDE.md)<br>[DOCUMENTATION_THEME_ORGANIZATION_PLAN.md](../archive/process_reports/2026_02/project/DOCUMENTATION_THEME_ORGANIZATION_PLAN.md) (归档) | 文档交叉引用指南<br>文档主题重组规划 |
| **架构** | [PROJECT_ARCHITECTURE_GUIDE.md](./PROJECT_ARCHITECTURE_GUIDE.md) | 项目架构设计 |
| **模板工具** | ONE_PAGE_SUMMARY_TEMPLATE.md | 一页纸总结模板 |

---

## 文档列表

- [KNOWLEDGE_STRUCTURE_FRAMEWORK.md](./KNOWLEDGE_STRUCTURE_FRAMEWORK.md) - 知识结构框架
- [MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md](./MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md) - 模块知识结构
- [DOCUMENTATION_CROSS_REFERENCE_GUIDE.md](./DOCUMENTATION_CROSS_REFERENCE_GUIDE.md) - 文档交叉引用
- [PROJECT_ARCHITECTURE_GUIDE.md](./PROJECT_ARCHITECTURE_GUIDE.md) - 项目架构
- [RUST_RELEASE_TRACKING_CHECKLIST.md](../archive/process_reports/2026_02/project/RUST_RELEASE_TRACKING_CHECKLIST.md) (归档) - 版本追踪
- [ARCHIVE_COMPLETION_REPORT.md](../ARCHIVE_COMPLETION_REPORT.md) - 归档完成报告

## 主索引

[00_MASTER_INDEX.md](../00_MASTER_INDEX.md)

---

[返回文档中心](../README.md)
