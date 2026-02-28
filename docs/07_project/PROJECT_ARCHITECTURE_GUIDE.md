# 项目架构指南

> **创建日期**: 2025-12-11
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [项目架构指南](#项目架构指南)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [代码示例](#代码示例)
    - [项目结构验证脚本](#项目结构验证脚本)
    - [模块依赖关系分析器](#模块依赖关系分析器)
    - [测试覆盖率报告生成器](#测试覆盖率报告生成器)
  - [形式化链接](#形式化链接)
    - [研究笔记关联](#研究笔记关联)
    - [实施场景](#实施场景)
  - [📋 概述 {#-概述}](#-概述--概述)
  - [🏗️ 项目结构 {#️-项目结构}](#️-项目结构-️-项目结构)
    - [整体架构](#整体架构)
  - [📦 模块设计 {#-模块设计}](#-模块设计--模块设计)
    - [模块分层](#模块分层)
      - [Tier 1: 基础层（C01-C03）](#tier-1-基础层c01-c03)
      - [Tier 2: 进阶层（C04-C06）](#tier-2-进阶层c04-c06)
      - [Tier 3: 应用层（C07-C10）](#tier-3-应用层c07-c10)
      - [Tier 4: 专业层（C11-C12）](#tier-4-专业层c11-c12)
  - [🔗 模块依赖关系 {#-模块依赖关系}](#-模块依赖关系--模块依赖关系)
    - [依赖图](#依赖图)
    - [依赖原则](#依赖原则)
  - [📚 文档架构 {#-文档架构}](#-文档架构--文档架构)
    - [4-Tier 文档体系](#4-tier-文档体系)
      - [Tier 1: 基础文档（Foundations）](#tier-1-基础文档foundations)
      - [Tier 2: 指南文档（Guides）](#tier-2-指南文档guides)
      - [Tier 3: 参考文档（References）](#tier-3-参考文档references)
      - [Tier 4: 高级文档（Advanced）](#tier-4-高级文档advanced)
  - [🎯 设计原则 {#-设计原则}](#-设计原则--设计原则)
    - [1. 模块化原则](#1-模块化原则)
    - [2. 可扩展性原则](#2-可扩展性原则)
    - [3. 可维护性原则](#3-可维护性原则)
  - [🔧 技术栈 {#-技术栈}](#-技术栈--技术栈)
    - [核心依赖](#核心依赖)
    - [开发工具](#开发工具)
  - [📊 性能考虑 {#-性能考虑}](#-性能考虑--性能考虑)
    - [1. 编译优化](#1-编译优化)
    - [2. 运行时优化](#2-运行时优化)
    - [3. 内存管理](#3-内存管理)
  - [🧪 测试策略 {#-测试策略}](#-测试策略--测试策略)
    - [测试层次](#测试层次)
    - [测试覆盖率目标](#测试覆盖率目标)
  - [📚 相关文档 {#-相关文档}](#-相关文档--相关文档)

---

## 代码示例

### 项目结构验证脚本

```rust
//! 验证项目架构一致性
use std::collections::HashSet;
use std::fs;
use std::path::Path;

struct ProjectStructureValidator {
    errors: Vec<String>,
}

impl ProjectStructureValidator {
    fn new() -> Self {
        Self { errors: Vec::new() }
    }

    fn validate_crate_structure(&mut self, crate_name: &str) {
        let crate_path = format!("crates/{}", crate_name);

        // 检查必需文件
        let required_files = vec![
            "Cargo.toml",
            "README.md",
            "src/lib.rs",
        ];

        for file in &required_files {
            let path = format!("{}/{}", crate_path, file);
            if !Path::new(&path).exists() {
                self.errors.push(format!(
                    "{}: 缺少必需文件 {}",
                    crate_name, file
                ));
            }
        }

        // 检查文档层级结构
        let doc_tiers = vec![
            "docs/tier_01_foundations",
            "docs/tier_02_guides",
            "docs/tier_03_references",
            "docs/tier_04_advanced",
        ];

        let docs_exist = doc_tiers.iter()
            .any(|tier| Path::new(&format!("{}/{}", crate_path, tier)).exists());

        if !docs_exist {
            self.errors.push(format!(
                "{}: 缺少文档层级结构",
                crate_name
            ));
        }
    }

    fn validate_dependency_direction(&mut self) {
        // 定义允许的依赖方向
        let tier1: HashSet<&str> = ["c01", "c02", "c03"].iter().cloned().collect();
        let tier2: HashSet<&str> = ["c04", "c05", "c06"].iter().cloned().collect();
        let tier3: HashSet<&str> = ["c07", "c08", "c09", "c10"].iter().cloned().collect();
        let tier4: HashSet<&str> = ["c11", "c12"].iter().cloned().collect();

        // 检查各 crate 的 Cargo.toml 依赖
        for entry in fs::read_dir("crates").unwrap().flatten() {
            let path = entry.path();
            if !path.is_dir() {
                continue;
            }

            let crate_name = path.file_name()
                .unwrap()
                .to_string_lossy()
                .to_string();

            let cargo_path = path.join("Cargo.toml");
            if let Ok(content) = fs::read_to_string(&cargo_path) {
                // 解析依赖，检查是否违反层级
                if let Some(dep_section) = content.find("[dependencies]") {
                    let deps = &content[dep_section..];
                    // 简化检查：Tier 4 不应该被 Tier 1-3 依赖
                    if tier1.iter().chain(tier2.iter()).chain(tier3.iter())
                        .any(|c| crate_name.starts_with(c)) {
                        for t4 in &tier4 {
                            if deps.contains(t4) {
                                self.errors.push(format!(
                                    "{}: 违反层级依赖，不应依赖 {}",
                                    crate_name, t4
                                ));
                            }
                        }
                    }
                }
            }
        }
    }

    fn report(&self) {
        if self.errors.is_empty() {
            println!("✅ 项目架构验证通过");
        } else {
            println!("❌ 发现 {} 个架构问题:\n", self.errors.len());
            for error in &self.errors {
                println!("- {}", error);
            }
        }
    }
}

fn main() {
    let mut validator = ProjectStructureValidator::new();

    // 验证所有 crate
    let crates = vec![
        "c01_ownership_borrow_scope",
        "c02_type_system",
        "c03_control_fn",
        "c04_generic",
        "c05_threads",
        "c06_async",
        "c07_process",
        "c08_algorithms",
        "c09_design_pattern",
        "c10_networks",
        "c11_macro_system",
        "c12_wasm",
    ];

    for crate_name in crates {
        validator.validate_crate_structure(crate_name);
    }

    // 验证依赖方向
    validator.validate_dependency_direction();

    validator.report();
}
```

### 模块依赖关系分析器

```rust
//! 分析模块间的依赖关系并生成可视化
use std::collections::{HashMap, HashSet};
use std::fs;

struct DependencyAnalyzer {
    dependencies: HashMap<String, HashSet<String>>,
}

impl DependencyAnalyzer {
    fn new() -> Self {
        Self {
            dependencies: HashMap::new(),
        }
    }

    fn analyze_crate(&mut self, crate_name: &str) {
        let cargo_path = format!("crates/{}/Cargo.toml", crate_name);

        if let Ok(content) = fs::read_to_string(&cargo_path) {
            let mut deps = HashSet::new();

            // 解析依赖（简化版）
            for line in content.lines() {
                let line = line.trim();
                // 检查是否为本项目内的 crate 依赖
                if line.starts_with("c0") && line.contains("=") {
                    let dep_name: String = line
                        .split('=')
                        .next()
                        .unwrap()
                        .trim()
                        .to_string();
                    if dep_name.starts_with("c0") {
                        deps.insert(dep_name);
                    }
                }
            }

            self.dependencies.insert(crate_name.to_string(), deps);
        }
    }

    fn generate_mermaid_graph(&self) -> String {
        let mut output = String::from("```mermaid\ngraph TD\n");

        for (crate_name, deps) in &self.dependencies {
            let short_name = crate_name.split('_').next().unwrap_or(crate_name);
            for dep in deps {
                let dep_short = dep.split('_').next().unwrap_or(dep);
                output.push_str(&format!(
                    "    {}[{}] --> {}[{}]\n",
                    short_name.to_uppercase(),
                    short_name.to_uppercase(),
                    dep_short.to_uppercase(),
                    dep_short.to_uppercase()
                ));
            }
        }

        output.push_str("```\n");
        output
    }

    fn detect_cycles(&self) -> Vec<Vec<String>> {
        let mut cycles = Vec::new();
        let mut visited = HashSet::new();
        let mut path = Vec::new();

        fn dfs(
            node: &str,
            deps: &HashMap<String, HashSet<String>>,
            visited: &mut HashSet<String>,
            path: &mut Vec<String>,
            cycles: &mut Vec<Vec<String>>
        ) {
            if path.contains(&node.to_string()) {
                // 发现环
                let cycle_start = path.iter().position(|x| x == node).unwrap();
                let cycle: Vec<String> = path[cycle_start..].iter()
                    .cloned()
                    .chain(std::iter::once(node.to_string()))
                    .collect();
                cycles.push(cycle);
                return;
            }

            if visited.contains(node) {
                return;
            }

            visited.insert(node.to_string());
            path.push(node.to_string());

            if let Some(neighbors) = deps.get(node) {
                for neighbor in neighbors {
                    dfs(neighbor, deps, visited, path, cycles);
                }
            }

            path.pop();
        }

        for crate_name in self.dependencies.keys() {
            dfs(crate_name, &self.dependencies, &mut visited, &mut path, &mut cycles);
        }

        cycles
    }
}

fn main() {
    let mut analyzer = DependencyAnalyzer::new();

    let crates = vec![
        "c01_ownership_borrow_scope",
        "c02_type_system",
        "c03_control_fn",
        "c04_generic",
        "c05_threads",
        "c06_async",
    ];

    for crate_name in crates {
        analyzer.analyze_crate(crate_name);
    }

    println!("=== 模块依赖图 ===");
    println!("{}", analyzer.generate_mermaid_graph());

    let cycles = analyzer.detect_cycles();
    if cycles.is_empty() {
        println!("✅ 未发现循环依赖");
    } else {
        println!("❌ 发现循环依赖:");
        for cycle in cycles {
            println!("  {:?}", cycle);
        }
    }
}
```

### 测试覆盖率报告生成器

```rust
//! 生成模块测试覆盖率报告
use std::collections::HashMap;
use std::process::Command;

struct CoverageReporter {
    targets: HashMap<String, f64>,
}

impl CoverageReporter {
    fn new() -> Self {
        let mut targets = HashMap::new();
        targets.insert("core".to_string(), 0.90);      // 核心库 90%+
        targets.insert("tool".to_string(), 0.80);      // 工具库 80%+
        targets.insert("example".to_string(), 0.60);   // 示例 60%+

        Self { targets }
    }

    fn check_coverage(&self, crate_name: &str, actual: f64) -> (bool, String) {
        // 根据 crate 类型确定目标
        let target = if crate_name.starts_with("c0") {
            self.targets["core"]
        } else {
            self.targets["tool"]
        };

        let passed = actual >= target;
        let status = if passed { "✅" } else { "❌" };

        (passed, format!(
            "{} {}: {:.1}% (目标: {:.0}%)",
            status, crate_name, actual * 100.0, target * 100.0
        ))
    }

    fn run_cargo_tarpaulin(&self, crate_name: &str) -> Option<f64> {
        // 使用 cargo tarpaulin 获取覆盖率
        let output = Command::new("cargo")
            .args(["tarpaulin", "-p", crate_name, "--out", "Stdout"])
            .output()
            .ok()?;

        let stdout = String::from_utf8(output.stdout).ok()?;

        // 解析覆盖率输出
        for line in stdout.lines() {
            if line.contains("% coverage") {
                // 提取百分比
                let percent: f64 = line
                    .split_whitespace()
                    .find(|w| w.ends_with('%'))?
                    .trim_end_matches('%')
                    .parse()
                    .ok()?;
                return Some(percent / 100.0);
            }
        }

        None
    }

    fn generate_report(&self) -> String {
        let mut report = String::from("# 测试覆盖率报告\n\n");
        report.push_str("| 模块 | 覆盖率 | 目标 | 状态 |\n");
        report.push_str("| :--- | :--- | :--- | :--- |\n");

        // 模拟数据
        let modules = vec![
            ("c01_ownership_borrow_scope", 0.92),
            ("c02_type_system", 0.88),
            ("c05_threads", 0.85),
        ];

        for (module, coverage) in modules {
            let (passed, _) = self.check_coverage(module, coverage);
            let status = if passed { "✅" } else { "❌" };
            let target = if module.starts_with("c0") { 0.90 } else { 0.80 };

            report.push_str(&format!(
                "| {} | {:.1}% | {:.0}% | {} |\n",
                module, coverage * 100.0, target * 100.0, status
            ));
        }

        report
    }
}

fn main() {
    let reporter = CoverageReporter::new();
    println!("{}", reporter.generate_report());
}
```

---

## 形式化链接

### 研究笔记关联

- **形式化方法**: [ownership_model.md](../research_notes/formal_methods/ownership_model.md) - 所有权模型的形式化定义
- **架构证明**: [PROOF_GRAPH_NETWORK.md](../04_thinking/PROOF_GRAPH_NETWORK.md) - 架构决策的形式化证明
- **知识结构**: [KNOWLEDGE_STRUCTURE_FRAMEWORK.md](./KNOWLEDGE_STRUCTURE_FRAMEWORK.md) - 知识依赖与模块关系

### 实施场景

| 场景 | 实施步骤 | 参考代码 |
| :--- | :--- | :--- |
| **新模块接入** | 1. 使用验证脚本检查结构<br>2. 确保依赖方向正确<br>3. 更新依赖图 | `ProjectStructureValidator` |
| **依赖分析** | 1. 运行依赖分析器<br>2. 检查循环依赖<br>3. 生成可视化 | `DependencyAnalyzer` |
| **质量监控** | 1. 运行覆盖率检查<br>2. 对比目标值<br>3. 生成报告 | `CoverageReporter` |

---

## 📋 概述 {#-概述}

本文档介绍 Rust 学习项目的整体架构设计，包括模块组织、依赖关系、设计原则等。

---

## 🏗️ 项目结构 {#️-项目结构}

### 整体架构

```text
rust-lang/
├── crates/              # 核心学习模块
│   ├── c01_ownership_borrow_scope/
│   ├── c02_type_system/
│   ├── c03_control_fn/
│   ├── c04_generic/
│   ├── c05_threads/
│   ├── c06_async/
│   ├── c07_process/
│   ├── c08_algorithms/
│   ├── c09_design_pattern/
│   ├── c10_networks/
│   ├── c11_macro_system/
│   └── c12_wasm/
├── docs/                # 项目文档
│   ├── quick_reference/  # 快速参考卡片
│   └── [其他文档]
├── examples/           # 综合示例
├── scripts/            # 工具脚本
└── tests/              # 集成测试
```

---

## 📦 模块设计 {#-模块设计}

### 模块分层

#### Tier 1: 基础层（C01-C03）

- **C01**: 所有权与借用
- **C02**: 类型系统
- **C03**: 控制流与函数

**特点**: 核心概念，所有学习者必须掌握

#### Tier 2: 进阶层（C04-C06）

- **C04**: 泛型编程
- **C05**: 线程与并发
- **C06**: 异步编程

**特点**: 高级特性，中级开发者需要掌握

#### Tier 3: 应用层（C07-C10）

- **C07**: 进程管理
- **C08**: 算法与数据结构
- **C09**: 设计模式
- **C10**: 网络编程

**特点**: 实际应用，高级开发者需要掌握

#### Tier 4: 专业层（C11-C12）

- **C11**: 宏系统
- **C12**: WASM

**特点**: 专业领域，专家级开发者需要掌握

---

## 🔗 模块依赖关系 {#-模块依赖关系}

### 依赖图

```text
C01 (所有权) ──┐
               ├──> C02 (类型系统) ──┐
C03 (控制流) ──┘                     ├──> C04 (泛型) ──┐
                                     │                  ├──> C05 (线程) ──┐
                                     │                  │                 ├──> C06 (异步) ──┐
                                     │                  │                 │                  ├──> C07 (进程)
                                     │                  │                 │                  ├──> C08 (算法)
                                     │                  │                 │                  ├──> C09 (设计模式)
                                     │                  │                 │                  ├──> C10 (网络)
                                     │                  │                 │                  ├──> C11 (宏)
                                     │                  │                 │                  └──> C12 (WASM)
```

### 依赖原则

1. **单向依赖**: 低层模块不依赖高层模块
2. **最小依赖**: 每个模块只依赖必要的模块
3. **接口隔离**: 通过 trait 和接口定义依赖

---

## 📚 文档架构 {#-文档架构}

### 4-Tier 文档体系

每个模块遵循统一的 4-Tier 文档架构：

#### Tier 1: 基础文档（Foundations）

- 项目概览
- 主索引导航
- 术语表
- 常见问题

#### Tier 2: 指南文档（Guides）

- 快速入门指南
- 实践指南
- 代码示例集合
- 实战项目集

#### Tier 3: 参考文档（References）

- API 参考
- 技术规范
- 性能优化参考
- 跨平台参考

#### Tier 4: 高级文档（Advanced）

- 高级主题
- 理论分析
- 最佳实践
- 研究笔记

---

## 🎯 设计原则 {#-设计原则}

### 1. 模块化原则

- **单一职责**: 每个模块只负责一个主题
- **高内聚**: 模块内部功能紧密相关
- **低耦合**: 模块之间依赖最小化

### 2. 可扩展性原则

- **特性标志**: 使用 feature flags 控制功能
- **插件架构**: 支持扩展和自定义
- **版本兼容**: 保持向后兼容

### 3. 可维护性原则

- **统一标准**: 所有模块遵循统一标准
- **文档完整**: 每个功能都有文档
- **测试覆盖**: 高测试覆盖率

---

## 🔧 技术栈 {#-技术栈}

### 核心依赖

```toml
[dependencies]
# 异步运行时
tokio = { version = "1.0", features = ["full"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
thiserror = "1.0"
anyhow = "1.0"

# 日志
tracing = "0.1"
tracing-subscriber = "0.3"
```

### 开发工具

```toml
[dev-dependencies]
# 测试框架
criterion = "0.5"  # 基准测试
tokio-test = "0.4"  # 异步测试

# 代码质量
clippy = "0.1"
rustfmt = "0.1"
```

---

## 📊 性能考虑 {#-性能考虑}

### 1. 编译优化

```toml
[profile.release]
opt-level = 3
lto = true
codegen-units = 1
```

### 2. 运行时优化

- 使用 `Arc` 而非 `Rc` 进行多线程共享
- 使用 `Box` 减少栈分配
- 使用迭代器而非循环
- 避免不必要的克隆

### 3. 内存管理

- 预分配容量（`Vec::with_capacity`）
- 使用 `Cow` 避免不必要的克隆
- 及时释放资源（RAII）

---

## 🧪 测试策略 {#-测试策略}

### 测试层次

1. **单元测试**: 测试单个函数/方法
2. **集成测试**: 测试模块间交互
3. **文档测试**: 确保示例代码正确
4. **性能测试**: 基准测试和性能分析

### 测试覆盖率目标

- **核心库**: 90%+
- **工具库**: 80%+
- **示例代码**: 60%+

---

## 📚 相关文档 {#-相关文档}

- [项目结构文档](./PROJECT_ARCHITECTURE_GUIDE.md)
- [最佳实践指南](../05_guides/BEST_PRACTICES.md)
- [测试覆盖率指南](../05_guides/TESTING_COVERAGE_GUIDE.md)
- [快速参考卡片](../02_reference/quick_reference/README.md)

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 持续更新
**最后更新**: 2026-01-26
