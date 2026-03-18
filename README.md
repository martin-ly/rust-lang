# Rust系统化学习项目

> **Rust版本**: 1.94.0
> **Edition**: 2024
> **状态**: 生产就绪 | 权威对齐

[![Rust](https://img.shields.io/badge/rust-1.94.0-blue.svg)](https://www.rust-lang.org)
[![Edition](https://img.shields.io/badge/edition-2024-purple.svg)](https://doc.rust-lang.org/edition-guide/rust-2024/)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](LICENSE)

---

## 项目简介

本项目是一个全面的Rust语言系统化学习资源，专注于：

- **现代化工具链**: Rust 1.94.0 + Edition 2024
- **权威内容对齐**: 引用PLDI 2025、POPL 2026等顶会论文
- **实践导向**: 12个学习crate覆盖核心概念
- **生产就绪**: 完整的CI/CD、Miri内存安全检查

---

## 快速开始

### 系统要求

```bash
rustc --version  # 需要 1.94.0+
cargo --version  # 需要 1.94.0+
```

### 安装与运行

```bash
# 克隆项目
git clone <repo-url>
cd rust-lang

# 安装工具链
rustup show  # 会自动读取rust-toolchain.toml

# 运行测试
cargo test --workspace
```

---

## 文档导航

所有文档位于 [`docs/`](docs/) 目录：

### 核心文档（根目录）

| 文档 | 描述 |
|------|------|
| [docs/2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md](docs/2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md) | **2026生态梳理** - 含权威引用 |
| [docs/AUTHORITATIVE_SOURCES_AND_CITATIONS.md](docs/AUTHORITATIVE_SOURCES_AND_CITATIONS.md) | 学术论文引用 |
| [docs/MIGRATION_GUIDE_2026.md](docs/MIGRATION_GUIDE_2026.md) | 迁移到Rust 1.94 |
| [docs/TERMINOLOGY_STANDARD.md](docs/TERMINOLOGY_STANDARD.md) | 术语标准 |

### 学习文档

| 目录 | 内容 |
|------|------|
| [docs/01_learning/](docs/01_learning/) | 学习规划、路径指南 |
| [docs/03_practice/](docs/03_practice/) | 实践项目 |
| [docs/05_guides/](docs/05_guides/) | 主题使用指南 |

### 更多文档

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md) - 完整索引
- [docs/README.md](docs/README.md) - 文档中心

---

## 项目结构

```
rust-lang/
├── README.md              # 📄 本文件
├── CONTRIBUTING.md        # 🤝 贡献指南
├── CHANGELOG.md           # 📝 变更日志
├── FAQ.md                 # ❓ 常见问题
├── Cargo.toml             # 📦 Workspace配置
├── rust-toolchain.toml    # ⚙️ 工具链配置
│
├── docs/                  # 📚 文档中心
│   ├── 2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md
│   ├── AUTHORITATIVE_SOURCES_AND_CITATIONS.md
│   ├── MIGRATION_GUIDE_2026.md
│   ├── 01_learning/       # 学习规划
│   ├── 05_guides/         # 使用指南
│   └── ...
│
├── crates/                # 📦 学习crate (c01-c12)
│   ├── c01_ownership/     # 所有权与借用
│   ├── c02_type_system/   # 类型系统
│   ├── ...
│   └── c12_wasm/          # WebAssembly
│
├── examples/              # 💡 示例代码
├── scripts/               # 🛠️ 脚本工具
└── tests/                 # 🧪 测试套件
```

---

## 核心特性

### Rust 1.94现代化

| 特性 | 状态 | 文档 |
|------|------|------|
| `array_windows` | ✅ 已集成 | [生态梳理](docs/2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md) |
| `LazyCell/LazyLock` API | ✅ 已迁移 | [迁移指南](docs/MIGRATION_GUIDE_2026.md) |
| Edition 2024 | ✅ 已准备 | [工具链](docs/06_toolchain/) |
| Miri Tree Borrows | ✅ CI配置 | [权威来源](docs/AUTHORITATIVE_SOURCES_AND_CITATIONS.md) |

### 学术权威对齐

- **Tree Borrows**: 引用PLDI 2025 Distinguished Paper
- **Miri**: 引用POPL 2026顶会论文

---

## 贡献指南

请阅读 [CONTRIBUTING.md](CONTRIBUTING.md) 了解如何参与。

---

## 许可证

[MIT许可证](LICENSE)

---

**维护者**: Rust学习项目团队
**最后更新**: 2026-03-18
**状态**: ✅ 生产就绪
