# 快速入门指南

> **最后更新**: 2026-03-08
> **Rust 版本**: 1.94.0+

---

## 🚀 5 分钟快速开始

### 1. 安装 Rust

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env
```

### 2. 验证安装

```bash
rustc --version  # rustc 1.94.0
cargo --version  # cargo 1.94.0
```

### 3. 运行第一个示例

```bash
cd crates/c01_ownership_borrow_scope
cargo run --example ownership_basics
```

---

## 📚 学习路径

| 阶段 | 时间 | 内容 | 入口 |
|------|------|------|------|
| 入门 | 1-2 周 | 所有权、类型、控制流 | [C01](./crates/c01_ownership_borrow_scope/README.md) |
| 进阶 | 2-4 周 | 泛型、并发、异步 | [C04](./crates/c04_generic/README.md) → [C05](./crates/c05_threads/README.md) → [C06](./crates/c06_async/README.md) |
| 高级 | 1-2 月 | 系统编程、网络、WASM | [C07](./crates/c07_process/README.md) → [C10](./crates/c10_networks/README.md) → [C12](./crates/c12_wasm/README.md) |

---

## 🔗 关键资源

- [QUICK_REFERENCE](./QUICK_REFERENCE.md) - 速查卡入口
- [LEARNING_CHECKLIST](./LEARNING_CHECKLIST.md) - 学习清单
- [docs/00_MASTER_INDEX](./docs/00_MASTER_INDEX.md) - 完整文档索引

---

*本指南是 Rust 学习项目的快速入门入口*
