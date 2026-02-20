# 文档主题梳理与重组规划
> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **归档日期**: 2026-02-20
> **归档原因**: 过程性文档归档
> **状态**: 📦 已归档

---


> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 全面规划文档内容主题结构，解决「乱、不成系统」问题

---

## 代码示例

### 文档分类自动化脚本

```rust
//! 自动分类 docs/ 目录下的文档
use std::collections::HashMap;
use std::fs;
use std::path::Path;

#[derive(Debug)]
enum DocCategory {
    Learning,    // 学习路径
    Reference,   // 速查参考
    Theory,      // 形式化理论
    Guides,      // 专题指南
    Toolchain,   // 工具链
    Project,     // 项目元文档
}

struct DocClassifier;

impl DocClassifier {
    fn classify_by_name(filename: &str) -> Option<DocCategory> {
        let name = filename.to_lowercase();
        
        if name.contains("learning") || name.contains("path") {
            Some(DocCategory::Learning)
        } else if name.contains("cheatsheet") || name.contains("reference") {
            Some(DocCategory::Reference)
        } else if name.contains("formal") || name.contains("proof") || name.contains("theory") {
            Some(DocCategory::Theory)
        } else if name.contains("guide") || name.contains("usage") {
            Some(DocCategory::Guides)
        } else if name.contains("toolchain") || name.contains("rust_1.") {
            Some(DocCategory::Toolchain)
        } else if name.contains("project") || name.contains("structure") {
            Some(DocCategory::Project)
        } else {
            None
        }
    }
    
    fn scan_directory(dir: &str) -> HashMap<DocCategory, Vec<String>> {
        let mut categories: HashMap<DocCategory, Vec<String>> = HashMap::new();
        
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().map_or(false, |e| e == "md") {
                    let filename = path.file_stem()
                        .unwrap()
                        .to_string_lossy()
                        .to_string();
                    
                    if let Some(category) = Self::classify_by_name(&filename) {
                        categories.entry(category)
                            .or_default()
                            .push(filename);
                    }
                }
            }
        }
        
        categories
    }
}

fn main() {
    let categories = DocClassifier::scan_directory("docs");
    
    for (category, files) in &categories {
        println!("{:?}: {} 个文档", category, files.len());
        for file in files.iter().take(5) {
            println!("  - {}", file);
        }
        if files.len() > 5 {
            println!("  ... 等共 {} 个", files.len());
        }
        println!();
    }
}
```

### 目录重组辅助工具

```rust
//! 文档主题重组规划辅助工具
use std::fs;
use std::io;
use std::path::Path;

struct ReorganizationPlan {
    /// 目标目录结构
    target_structure: Vec<(String, Vec<String>)>,
}

impl ReorganizationPlan {
    fn new() -> Self {
        let structure = vec![
            ("01_learning".to_string(), vec![
                "LEARNING_PATH_PLANNING.md".to_string(),
                "OFFICIAL_RESOURCES_MAPPING.md".to_string(),
            ]),
            ("02_reference".to_string(), vec![
                "quick_reference/".to_string(),
                "EDGE_CASES_AND_SPECIAL_CASES.md".to_string(),
            ]),
            ("03_theory".to_string(), vec![
                "research_notes/".to_string(),
            ]),
            ("04_thinking".to_string(), vec![
                "THINKING_REPRESENTATION_METHODS.md".to_string(),
                "DECISION_GRAPH_NETWORK.md".to_string(),
                "PROOF_GRAPH_NETWORK.md".to_string(),
            ]),
            ("05_guides".to_string(), vec![
                "ASYNC_PROGRAMMING_USAGE_GUIDE.md".to_string(),
                "THREADS_CONCURRENCY_USAGE_GUIDE.md".to_string(),
            ]),
            ("06_toolchain".to_string(), vec![
                "rust_1.93_*.md".to_string(),
            ]),
            ("07_project".to_string(), vec![
                "KNOWLEDGE_STRUCTURE_FRAMEWORK.md".to_string(),
                "RUST_RELEASE_TRACKING_CHECKLIST.md".to_string(),
            ]),
        ];
        
        Self {
            target_structure: structure,
        }
    }
    
    fn generate_plan(&self) -> String {
        let mut output = String::from("# 文档重组执行计划\n\n");
        
        for (idx, (dir, files)) in self.target_structure.iter().enumerate() {
            output.push_str(&format!("## 阶段 {}: {}\n\n", idx + 1, dir));
            output.push_str(&format!("目标目录: `docs/{}`\n\n", dir));
            output.push_str("包含文档:\n");
            for file in files {
                output.push_str(&format!("- {}\n", file));
            }
            output.push_str("\n");
        }
        
        output
    }
}

fn main() -> io::Result<()> {
    let plan = ReorganizationPlan::new();
    fs::write("docs/reorganization_plan.md", plan.generate_plan())?;
    println!("重组计划已生成: docs/reorganization_plan.md");
    Ok(())
}
```

### 文件名规范化检查

```rust
//! 检查文档命名规范
use std::fs;
use regex::Regex;

struct NamingConventionChecker {
    issues: Vec<(String, String)>,
}

impl NamingConventionChecker {
    fn new() -> Self {
        Self { issues: Vec::new() }
    }
    
    fn check_file(&mut self, filename: &str) {
        // 检查混合命名
        if filename.contains('_') && filename.contains('-') {
            self.issues.push((
                filename.to_string(),
                "同时使用下划线和连字符".to_string()
            ));
        }
        
        // 检查版本号格式
        let version_regex = Regex::new(r"RUST_1\.\d{2}").unwrap();
        if filename.to_uppercase().contains("RUST_") 
            && !version_regex.is_match(filename) {
            self.issues.push((
                filename.to_string(),
                "版本号格式不规范，应使用 RUST_1.XX".to_string()
            ));
        }
        
        // 检查中英文混合
        if filename.chars().any(|c| c as u32 > 127) {
            self.issues.push((
                filename.to_string(),
                "文件名包含中文字符".to_string()
            ));
        }
    }
    
    fn check_directory(&mut self, dir: &str) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().map_or(false, |e| e == "md") {
                    if let Some(name) = path.file_stem() {
                        self.check_file(&name.to_string_lossy());
                    }
                }
            }
        }
    }
    
    fn report(&self) {
        if self.issues.is_empty() {
            println!("✅ 所有文档命名符合规范");
        } else {
            println!("⚠️ 发现 {} 个命名问题:\n", self.issues.len());
            for (file, issue) in &self.issues {
                println!("- {}: {}", file, issue);
            }
        }
    }
}

fn main() {
    let mut checker = NamingConventionChecker::new();
    checker.check_directory("docs");
    checker.report();
}
```

---

## 形式化链接

### 研究笔记关联

- **知识结构**: [KNOWLEDGE_STRUCTURE_FRAMEWORK.md](./KNOWLEDGE_STRUCTURE_FRAMEWORK.md) - 知识结构框架定义
- **项目架构**: [PROJECT_ARCHITECTURE_GUIDE.md](./PROJECT_ARCHITECTURE_GUIDE.md) - 项目整体架构设计
- **交叉引用**: [DOCUMENTATION_CROSS_REFERENCE_GUIDE.md](./DOCUMENTATION_CROSS_REFERENCE_GUIDE.md) - 文档交叉引用指南

### 实施场景

| 阶段 | 实施步骤 | 工具/脚本 |
| :--- | :--- | :--- |
| **阶段 1: 索引构建** | 1. 使用分类脚本扫描现有文档<br>2. 建立主题 → 文档映射<br>3. 更新 00_MASTER_INDEX | `DocClassifier::scan_directory()` |
| **阶段 2: 合并归档** | 1. 使用重组规划工具<br>2. 移动文件到归档目录<br>3. 更新相对链接 | `ReorganizationPlan::generate_plan()` |
| **阶段 3: 目录重组** | 1. 检查命名规范<br>2. 创建新目录结构<br>3. 批量移动文件 | `NamingConventionChecker` |

---

## 一、现状问题诊断

### 1.1 根目录扁平化 overload

`docs/` 根目录有 **40+ 个 .md 文件**，未按主题分类，查找困难：

| 类别 | 文件示例 | 问题 |
| :--- | :--- | :--- || **专题指南** | ASYNC_PROGRAMMING_USAGE_GUIDE, DESIGN_PATTERNS_USAGE_GUIDE, MACRO_SYSTEM_USAGE_GUIDE, THREADS_CONCURRENCY_USAGE_GUIDE, WASM_USAGE_GUIDE, UNSAFE_RUST_GUIDE, TROUBLESHOOTING_GUIDE | 分散，无统一入口 |
| **思维表征** | THINKING_REPRESENTATION_METHODS, DECISION_GRAPH_NETWORK, PROOF_GRAPH_NETWORK, MIND_MAP_COLLECTION, MULTI_DIMENSIONAL_CONCEPT_MATRIX, APPLICATIONS_ANALYSIS_VIEW | 6 个文件，概念重叠 |
| **知识结构** | KNOWLEDGE_STRUCTURE_FRAMEWORK, MODULE_KNOWLEDGE_STRUCTURE_GUIDE, DOCUMENTATION_CROSS_REFERENCE_GUIDE, FINAL_DOCUMENTATION_COMPLETION_GUIDE | 层次不清 |
| **版本相关** | RUST_192_* (6 个), MODULE_1.93_ADAPTATION_STATUS, RUST_RELEASE_TRACKING_CHECKLIST | 与 toolchain 重复 |
| **报告/评估** | PROJECT_CRITICAL_EVALUATION_REPORT, IMPROVEMENT_COMPLETION_SUMMARY, PLAN_IMPLEMENTATION_COMPLETION, LINK_FIX_PLAN | 元文档、过程性文档 |
| **对比/分析** | CROSS_LANGUAGE_COMPARISON, CROSS_MODULE_INTEGRATION_EXAMPLES, EDGE_CASES_AND_SPECIAL_CASES, STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS, OFFICIAL_RESOURCES_MAPPING | 未归入主题 |
| **最佳实践** | BEST_PRACTICES_GUIDE, COMPREHENSIVE_BEST_PRACTICES | 重复 |
| **性能/测试** | PERFORMANCE_TUNING_GUIDE, PERFORMANCE_TESTING_REPORT, TESTING_COVERAGE_GUIDE | 可归入 guides 或 toolchain |
| **其他** | ADVANCED_TOPICS_DEEP_DIVE, PROJECT_ARCHITECTURE_GUIDE, LEARNING_PATH_PLANNING | 分散 |

### 1.2 结构性问题

| 问题 | 说明 |
| :--- | :--- || **嵌套 docs/docs** | `docs/docs/language/applications/14_workflow/` 仅 2 个文件，层级过深且孤立 |
| **rust-formal-engineering-system 空心化** | 多数子目录为 README 占位， real 内容在 research_notes，形成「映射层」而非「内容层」 |
| **双重入口** | 形式化理论：rust-formal-engineering-system 与 research_notes 两套入口，易混淆 |
| **命名不一致** | 中英文混用、RUST_192 vs 1.92、GUIDE vs 指南、COMPREHENSIVE vs 全面 |
| **模块文档与根文档割裂** | crates/*/docs 与 docs/ 主题对应关系不清晰 |

### 1.3 主题重叠与冗余

| 重叠域 | 涉及文档 | 建议 |
| :--- | :--- | :--- || 形式化理论 | rust-formal-engineering-system, research_notes, PROOF_INDEX, PROOF_GRAPH_NETWORK, THINKING_REPRESENTATION_METHODS 证明树 | 统一入口，减少跳转 |
| 最佳实践 | BEST_PRACTICES_GUIDE, COMPREHENSIVE_BEST_PRACTICES | 合并 |
| 思维表征 | 6 个独立文件 | 归入单一「思维表征」主题 |
| 版本信息 | RUST_192_*, toolchain/*, MODULE_1.93_* | 版本相关统一归 toolchain |

---

## 二、目标主题结构（建议）

### 2.1 顶层分类原则

```
按「用户意图」分类，而非按「文档类型」：
├── 我要学习 → 学习路径、模块、速查
├── 我要参考 → 速查卡、API、标准库
├── 我要理解 → 理论、形式化、思维表征
├── 我要实践 → 指南、应用、示例
├── 我要对齐 → 版本、工具链、官方映射
└── 我要维护 → 项目元文档、规划、报告
```

### 2.2 建议目录结构

```text
docs/
├── README.md                    # 主入口（精简，链到各主题）
│
├── 01_learning/                 # 学习路径与导航
│   ├── README.md                    # 学习入口
│   ├── LEARNING_PATH_PLANNING.md
│   ├── OFFICIAL_RESOURCES_MAPPING.md
│   └── module_index.md               # 与 crates 映射
│
├── 02_reference/                # 参考与速查
│   ├── quick_reference/             # 20 个速查卡（含 AI/ML）
│   ├── EDGE_CASES_AND_SPECIAL_CASES.md
│   ├── STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md
│   └── CROSS_LANGUAGE_COMPARISON.md
│
├── 03_theory/                   # 理论与形式化
│   ├── README.md                    # 理论入口（统一入口）
│   ├── research_notes/              # 形式化方法、类型理论（保留）
│   ├── rust-formal-engineering-system/  # 保留或合并为索引
│   └── PROOF_INDEX.md → research_notes/PROOF_INDEX
│
├── 04_thinking/                 # 思维表征（整合）
│   ├── README.md                    # 思维表征总入口
│   ├── THINKING_REPRESENTATION_METHODS.md
│   ├── DECISION_GRAPH_NETWORK.md
│   ├── PROOF_GRAPH_NETWORK.md
│   ├── MIND_MAP_COLLECTION.md
│   ├── MULTI_DIMENSIONAL_CONCEPT_MATRIX.md
│   └── APPLICATIONS_ANALYSIS_VIEW.md
│
├── 05_guides/                   # 专题指南（整合）
│   ├── README.md                    # 指南目录
│   ├── async/                        # ASYNC_PROGRAMMING_USAGE_GUIDE
│   ├── threads/                      # THREADS_CONCURRENCY_USAGE_GUIDE
│   ├── design_patterns/               # DESIGN_PATTERNS_USAGE_GUIDE
│   ├── macros/                       # MACRO_SYSTEM_USAGE_GUIDE
│   ├── wasm/                         # WASM_USAGE_GUIDE
│   ├── unsafe/                      # UNSAFE_RUST_GUIDE
│   ├── troubleshooting/              # TROUBLESHOOTING_GUIDE
│   ├── performance/                  # PERFORMANCE_TUNING_GUIDE, PERFORMANCE_TESTING_REPORT
│   ├── testing/                      # TESTING_COVERAGE_GUIDE
│   └── best_practices/               # 合并 BEST_PRACTICES
│
├── 06_toolchain/                # 工具链与版本（保留）
│   └── [现有 11 个文件 + 版本演进]
│
├── 07_project/                  # 项目元文档
│   ├── KNOWLEDGE_STRUCTURE_FRAMEWORK.md
│   ├── MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md
│   ├── DOCUMENTATION_CROSS_REFERENCE_GUIDE.md
│   ├── RUST_RELEASE_TRACKING_CHECKLIST.md
│   ├── MODULE_1.93_ADAPTATION_STATUS.md
│   └── archive/                      # 归档
│
├── CROSS_MODULE_INTEGRATION_EXAMPLES.md  # 可保留根目录或入 05_guides
│
└── archive/                     # 归档（保留）
```

### 2.3 主题与文档映射表

| 主题 | 现文档 | 建议位置 |
| :--- | :--- | :--- || 学习路径 | LEARNING_PATH_PLANNING, OFFICIAL_RESOURCES_MAPPING | 01_learning |
| 速查 | quick_reference 目录 | 02_reference/quick_reference |
| 边界特例 | EDGE_CASES_AND_SPECIAL_CASES | 02_reference |
| 标准库分析 | STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS | 02_reference |
| 跨语言对比 | CROSS_LANGUAGE_COMPARISON | 02_reference |
| 形式化理论 | research_notes, rust-formal-engineering-system | 03_theory |
| 证明索引 | PROOF_INDEX | 03_theory（或 research_notes） |
| 思维表征 | 6 个文件 | 04_thinking |
| 专题指南 | 7+ 个 *_USAGE_GUIDE | 05_guides |
| 最佳实践 | BEST_PRACTICES_GUIDE, COMPREHENSIVE_BEST_PRACTICES | 05_guides/best_practices（合并） |
| 工具链 | toolchain 目录 | 06_toolchain |
| 版本 | RUST_192_*, MODULE_1.93_* | 06_toolchain 或 07_project |
| 知识结构 | KNOWLEDGE_STRUCTURE_FRAMEWORK, MODULE_KNOWLEDGE_STRUCTURE_GUIDE | 07_project |
| 报告/评估 | PLAN_IMPLEMENTATION, CRITICAL_EVALUATION, IMPROVEMENT_SUMMARY, LINK_FIX_PLAN | 07_project 或 archive |

---

## 三、执行策略（分阶段）

### 阶段 1：不移动文件，先建索引（低风险）

1. 新建 `docs/00_MASTER_INDEX.md` 作为文档总入口
2. 按「主题」分类列出所有文档，建立「主题 → 文档」映射
3. 更新 `docs/README.md`，按主题分块展示，替代当前扁平列表

**交付**：清晰的导航入口，无需移动文件

### 阶段 2：合并与归档（中风险）

1. 合并 BEST_PRACTICES_GUIDE + COMPREHENSIVE_BEST_PRACTICES → 单一最佳实践文档
2. 将 RUST_192_* 6 个文件迁入 `archive/version_reports/` 或 `toolchain/version_reports/`
3. 将 PLAN_IMPLEMENTATION、LINK_FIX_PLAN 等过程性文档迁入 archive/ 或 07_project/

**交付**：根目录文件数量减少约 15 个

### 阶段 3：主题目录重组（中高风险）

1. 新建 01_learning、02_reference、04_thinking、05_guides、07_project 目录
2. 按映射表移动文件（保持相对路径可读性）
3. 批量更新所有文档中的内部链接

**交付**：按主题分层，结构清晰

### 阶段 4：rust-formal-engineering-system 整合（可选）

1. 若保留：将 00_master_index 作为唯一入口，子目录 README 仅保留「映射到 research_notes」说明
2. 若合并：将 rust-formal-engineering-system 作为 03_theory 下的子目录，或直接并入 research_notes 的导航

**交付**：形式化理论单一入口

---

## 四、命名规范建议

| 维度 | 规范 | 示例 |
| :--- | :--- | :--- || 主题目录 | 数字前缀 + 英文小写 | 01_learning, 02_reference |
| 文档文件名 | 英文大写 + 描述性 | THINKING_REPRESENTATION_METHODS.md |
| 版本文档 | 统一 `toolchain/` 或 `version/` 前缀 | toolchain/07_rust_1.93_full_changelog.md |
| 速查卡 | 保持现有 `*_cheatsheet.md` | ownership_cheatsheet.md |
| 中文文档 | 模块内 doc 可保留中文 | crates/c01_ownership_borrow_scope/docs/ |

---

## 五、docs/README 重构建议

当前 README 按「四大文档系统」组织，但未覆盖根目录大量文件。建议改为：

```markdown
# 文档中心

## 按主题快速导航

| 主题 | 入口 | 说明 |
| :--- | :--- | :--- || 学习路径 | 01_learning/ | 学习规划、官方资源映射 |
| 速查参考 | 02_reference/quick_reference/ | 20 个速查卡 |
| 形式化理论 | 03_theory/ | 研究笔记、证明索引 |
| 思维表征 | 04_thinking/ | 思维导图、决策树、证明树、矩阵 |
| 专题指南 | 05_guides/ | 异步、线程、WASM、Unsafe 等 |
| 工具链 | 06_toolchain/ | 编译器、Cargo、版本演进 |
| 项目元文档 | 07_project/ | 知识结构、版本追踪 |

## 按角色导航

- 初学者 → 学习路径 → 速查卡 → C01 模块
- 开发者 → 专题指南 → 速查卡 → 边界特例
- 研究者 → 形式化理论 → 思维表征 → 证明索引
- 维护者 → 项目元文档 → 版本追踪
```

---

## 六、与 crates 的映射关系

| 主题 | 对应 crates | 说明 |
| :--- | :--- | :--- || 所有权 | c01_ownership_borrow_scope | 根 docs 与 c01/docs 互补 |
| 类型系统 | c02_type_system | |
| 控制流 | c03_control_fn | |
| 泛型 | c04_generic | |
| 线程 | c05_threads | 对应 THREADS_CONCURRENCY_USAGE_GUIDE |
| 异步 | c06_async | 对应 ASYNC_PROGRAMMING_USAGE_GUIDE |
| 进程 | c07_process | |
| 算法 | c08_algorithms | |
| 设计模式 | c09_design_pattern | 对应 DESIGN_PATTERNS_USAGE_GUIDE |
| 网络 | c10_networks | |
| 宏 | c11_macro_system | 对应 MACRO_SYSTEM_USAGE_GUIDE |
| WASM | c12_wasm | 对应 WASM_USAGE_GUIDE |

**原则**：根 docs 提供「跨模块视图、指南、速查」；crates/*/docs 提供「模块内深度内容」。

---

## 七、总结

| 问题 | 规划方向 |
| :--- | :--- || 根目录扁平、杂乱 | 按主题分层（01–07） |
| 思维表征分散 | 归入 04_thinking |
| 指南分散 | 归入 05_guides |
| 形式化理论双入口 | 统一为 03_theory |
| 版本/报告混杂 | 归入 06_toolchain / 07_project |
| 最佳实践重复 | 合并 |
| docs/docs 嵌套 | 迁移或归档 |

**建议执行顺序**：阶段 1 → 阶段 2 → 阶段 3；阶段 4 视情况而定。

---

**维护者**: 文档规划组
**创建日期**: 2026-02-12
