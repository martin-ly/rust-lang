# Incremental Practice

> **定位**: Rust 增量编译（Incremental Compilation）可观测实验。

---

## 内容

本目录包含三个小模块：`math`、`greet`、`analyze`，用于演示 `rustc` 增量编译的 Red-Green 算法：

- 冷编译：所有查询首次执行
- 无修改重编译：大量查询复用
- 修改后重编译：仅受影响查询重新执行

---

## 运行

```bash
cd examples/incremental_practice
cargo test

# 观察增量编译信息（需要 nightly）
RUSTFLAGS="-Z incremental-info" cargo +nightly build
```
---

## 延伸阅读

- `concept/04_formal/19_rustc_query_system.md`
