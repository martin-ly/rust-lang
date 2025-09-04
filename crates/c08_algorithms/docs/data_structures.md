# 数据结构实现（Rust 1.89 对齐）

本页对齐国际百科的数据结构目录，列出本仓库已提供的实现与用法，并标注与算法模块的配合要点。

---

## 线性结构

- 栈（Stack）：`src/data_structure/stack.rs`

示例：

```rust
use c08_algorithms::data_structure::stack::Stack;

fn demo_stack() {
    let mut s = Stack::new();
    s.push(1);
    s.push(2);
    assert_eq!(s.pop(), Some(2));
    assert_eq!(s.peek(), Some(&1));
}
```

---

## 并发/性能相关结构（示例）

- 原子计数器、简易线程池、简化无锁结构：`src/performance_examples/concurrency_optimization.rs`
- 性能优化工具与配置：`src/performance_examples/*`, `src/performance_optimization.rs`

---

## 图与树（目录占位）

- 图的表示：邻接表 `HashMap<T, Vec<T>>` 已在 `searching` 与 `graph` 模块的算法中广泛使用
- 树/堆/平衡树：堆在排序中已有使用；其他树结构将按目录逐步补齐

---

更多示例与异步/并行策略：见 `docs/rust_189_features.md` 与基准 `benches/alg_benches.rs`。
