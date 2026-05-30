# 项目结构说明

> **分级**: [B]
> **Bloom 层级**: L2-L3 (理解/应用)

> **最后更新**: 2026-04-10
> **Rust 版本**: 1.96.0
> **Edition**: 2024

---

## 目录概览
>
> **[来源: Rust Official Docs]**

```
rust-lang/
├── docs/                   # 文档中心
├── crates/                 # 代码 crate
├── examples/               # 示例代码
├── scripts/                # 脚本工具
├── tests/                  # 集成测试
├── Cargo.toml             # Workspace 配置
├── README.md              # 项目说明
└── 10_contributing.md        # 贡献指南
```

---

## 文档结构 (docs/)
>
> **[来源: Rust Official Docs]**

```
docs/
├── 00_master_index.md                  # 主索引
├── ARCHITECTURE.md                      # 架构文档
├── 10_project_structure.md                 # 本文件
├── 10_api_guide.md                         # API 指南
├── 10_dependency_graph.md                  # 依赖图
├── 10_2026_rust_ecosystem_comprehensive_review_with_citations.md
├── 10_authoritative_sources_and_citations.md
├── 10_migration_guide_2026.md
├── TERMINOLOGY_STANDARD.md
├── 01_learning/                         # 学习文档
├── 03_practice/                         # 实践项目
├── 05_guides/                           # 主题指南
├── 06_toolchain/                        # 工具链
├── 07_project/                          # 项目管理
└── 09_references/                       # 参考文档
```

---

## Crate 结构 (crates/)
>
> **[来源: Rust Official Docs]**

### 核心学习 Crate
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

| Crate | 目录 | 描述 | 状态 |
|-------|------|------|------|
| c01_ownership | crates/c01_ownership_borrow_scope/ | 所有权与借用 | 完整 |
| c02_type_system | crates/c02_type_system/ | 类型系统 | 完整 |
| c03_control_fn | crates/c03_control_fn/ | 控制流与函数 | 完整 |
| c04_generic | crates/c04_generic/ | 泛型与 Trait | 完整 |
| c05_threads | crates/c05_threads/ | 线程与并发 | 完整 |
| c06_async | crates/c06_async/ | 异步编程 | 完整 |
| c07_process | crates/c07_process/ | 进程管理 | 完整 |
| c08_algorithms | crates/c08_algorithms/ | 算法与数据结构 | 完整 |
| c09_design_pattern | crates/c09_design_pattern/ | 设计模式 | 完整 |
| c10_networks | crates/c10_networks/ | 网络编程 | 完整 |
| c11_macro_system | crates/c11_macro_system/ | 宏系统 | 完整 |
| c12_wasm | crates/c12_wasm/ | WebAssembly | 完整 |

### 共享 Crate
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| Crate | 目录 | 描述 |
|-------|------|------|
| common | crates/common/ | 共享库、工具函数 |
| integration_tests | crates/integration_tests/ | 集成测试套件 |

### Crate 标准结构
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```
crates/cXX_name/
├── src/
│   ├── lib.rs              # 库入口
│   ├── bin/                # 可执行文件
│   └── */                  # 模块目录
├── examples/               # 示例代码
├── tests/                  # 单元测试
├── benches/                # 基准测试
├── docs/                   # 模块文档
├── Cargo.toml             # 配置
└── README.md              # 模块说明
```

---

## 示例结构 (examples/)
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```
examples/
├── basic/                  # 基础示例
├── advanced/               # 高级示例
└── integration/            # 集成示例
```

---

## 脚本工具 (scripts/)
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```
scripts/
├── build/                  # 构建脚本
├── test/                   # 测试脚本
├── ci/                     # CI/CD 脚本
└── util/                   # 工具脚本
```

---

## 测试结构
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### 单元测试
>
> **[来源: [crates.io](https://crates.io/)]**

- 位置: crates/*/tests/ 或 src/ 内 #[cfg(test)]
- 命令: cargo test -p <crate>

### 集成测试
>
> **[来源: [docs.rs](https://docs.rs/)]**

- 位置: crates/integration_tests/
- 命令: cargo test -p integration_tests

### 基准测试
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- 位置: crates/*/benches/
- 命令: cargo bench -p <crate>

---

## 配置文件
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### Cargo Workspace
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```toml
[workspace]
members = [
    "crates/c01_ownership_borrow_scope",
    "crates/c02_type_system",
]

[workspace.dependencies]
tokio = "1.51"
serde = "1.0"
```

### 工具链配置
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 文件 | 用途 |
|------|------|
| rust-toolchain.toml | Rust 版本锁定 |
| rustfmt.toml | 格式化配置 |
| clippy.toml | Lint 配置 |
| deny.toml | 依赖审计 |
| tarpaulin.toml | 覆盖率配置 |

---

## 命名约定
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 文件命名
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

| 类型 | 格式 | 示例 |
|------|------|------|
| Rust 源文件 | snake_case.rs | my_module.rs |
| 测试文件 | <name>_test.rs | math_test.rs |
| 示例文件 | <description>_example.rs | tcp_echo_example.rs |
| 文档文件 | UPPER_SNAKE_CASE.md | 10_api_guide.md |

### Crate 命名
>
> **[来源: [crates.io](https://crates.io/)]**

```
cXX_<描述>          # 学习 crate
common              # 共享库
integration_tests   # 集成测试
```

---

## 依赖管理
>
> **[来源: [docs.rs](https://docs.rs/)]**

### 版本策略
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

| 级别 | 策略 |
|------|------|
| Workspace | 在根 Cargo.toml 统一管理 |
| Crate | 通过 workspace = true 引用 |
| Dev | 在各自 Cargo.toml 指定 |

---

## CI/CD 集成
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### GitHub Actions (.github/workflows/)
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```
.github/workflows/
├── ci.yml                 # 主 CI 流程
├── test.yml               # 测试流程
├── lint.yml               # 代码检查
└── docs.yml               # 文档部署
```

### 质量检查
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- 编译: cargo build --workspace
- 测试: cargo test --workspace
- 格式化: cargo fmt --check
- Lint: cargo clippy --workspace
- 文档: cargo doc --workspace
- 安全: cargo audit

---

## 相关文档
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- ARCHITECTURE.md - 架构总览
- 10_api_guide.md - API 使用指南
- 10_dependency_graph.md - 依赖关系
- ../10_contributing.md - 贡献指南

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library]**

> **[来源: ACM - Systems Programming]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

> **[来源: Rustonomicon]**

---

## 权威来源索引

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
