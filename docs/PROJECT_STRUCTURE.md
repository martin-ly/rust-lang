# 项目结构说明

> **最后更新**: 2026-04-10
> **Rust 版本**: 1.96.0
> **Edition**: 2024

---

## 目录概览

```
rust-lang/
├── docs/                   # 文档中心
├── crates/                 # 代码 crate
├── examples/               # 示例代码
├── scripts/                # 脚本工具
├── tests/                  # 集成测试
├── Cargo.toml             # Workspace 配置
├── README.md              # 项目说明
└── CONTRIBUTING.md        # 贡献指南
```

---

## 文档结构 (docs/)

```
docs/
├── 00_master_index.md                  # 主索引
├── ARCHITECTURE.md                      # 架构文档
├── PROJECT_STRUCTURE.md                 # 本文件
├── API_GUIDE.md                         # API 指南
├── DEPENDENCY_GRAPH.md                  # 依赖图
├── 2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md
├── AUTHORITATIVE_SOURCES_AND_CITATIONS.md
├── MIGRATION_GUIDE_2026.md
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

### 核心学习 Crate

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

| Crate | 目录 | 描述 |
|-------|------|------|
| common | crates/common/ | 共享库、工具函数 |
| integration_tests | crates/integration_tests/ | 集成测试套件 |

### Crate 标准结构

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

```
examples/
├── basic/                  # 基础示例
├── advanced/               # 高级示例
└── integration/            # 集成示例
```

---

## 脚本工具 (scripts/)

```
scripts/
├── build/                  # 构建脚本
├── test/                   # 测试脚本
├── ci/                     # CI/CD 脚本
└── util/                   # 工具脚本
```

---

## 测试结构

### 单元测试

- 位置: crates/*/tests/ 或 src/ 内 #[cfg(test)]
- 命令: cargo test -p <crate>

### 集成测试

- 位置: crates/integration_tests/
- 命令: cargo test -p integration_tests

### 基准测试

- 位置: crates/*/benches/
- 命令: cargo bench -p <crate>

---

## 配置文件

### Cargo Workspace

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

| 文件 | 用途 |
|------|------|
| rust-toolchain.toml | Rust 版本锁定 |
| rustfmt.toml | 格式化配置 |
| clippy.toml | Lint 配置 |
| deny.toml | 依赖审计 |
| tarpaulin.toml | 覆盖率配置 |

---

## 命名约定

### 文件命名

| 类型 | 格式 | 示例 |
|------|------|------|
| Rust 源文件 | snake_case.rs | my_module.rs |
| 测试文件 | <name>_test.rs | math_test.rs |
| 示例文件 | <description>_example.rs | tcp_echo_example.rs |
| 文档文件 | UPPER_SNAKE_CASE.md | API_GUIDE.md |

### Crate 命名

```
cXX_<描述>          # 学习 crate
common              # 共享库
integration_tests   # 集成测试
```

---

## 依赖管理

### 版本策略

| 级别 | 策略 |
|------|------|
| Workspace | 在根 Cargo.toml 统一管理 |
| Crate | 通过 workspace = true 引用 |
| Dev | 在各自 Cargo.toml 指定 |

---

## CI/CD 集成

### GitHub Actions (.github/workflows/)

```
.github/workflows/
├── ci.yml                 # 主 CI 流程
├── test.yml               # 测试流程
├── lint.yml               # 代码检查
└── docs.yml               # 文档部署
```

### 质量检查

- 编译: cargo build --workspace
- 测试: cargo test --workspace
- 格式化: cargo fmt --check
- Lint: cargo clippy --workspace
- 文档: cargo doc --workspace
- 安全: cargo audit

---

## 相关文档

- ARCHITECTURE.md - 架构总览
- API_GUIDE.md - API 使用指南
- DEPENDENCY_GRAPH.md - 依赖关系
- ../CONTRIBUTING.md - 贡献指南
