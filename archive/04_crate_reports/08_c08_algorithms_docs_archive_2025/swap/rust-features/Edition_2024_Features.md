# Edition 2024 / Rust 1.90 稳定语法要点（本仓实例）

- let-else：`topics/searching/mod.rs`、`machine_learning/kmeans.rs`、`data_structure/priority_queue.rs`
- Option::is_some_and：`graph/mod.rs`、`topics/searching/mod.rs`
- 返回位置 impl Trait（RPITIT）：`algorithms/sorting/mod.rs::best_summary_iter`、`machine_learning/*::*_iter`、`graph/mod.rs::zero_indegree_keys`
- 从不返回类型 `!` 示例：`algorithms/rust_2024_features.rs::abort_with`
- 统一示例：`algorithms/rust_2024_features.rs` 与 `examples/rust_2024_features_demo.rs`

验证方式：

```bash
cargo check -p c08_algorithms
cargo test -p c08_algorithms
cargo run -p c08_algorithms --example rust_2024_features_demo
```
