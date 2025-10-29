# 并发正确性（Miri/Loom）

- Miri：检测未定义行为；在 CI 对关键 crate 运行子集用例
  - 使用：`cargo +nightly miri test -p c05_threads`（按需开启）
- Loom：探索不同调度以发现竞态/死锁
  - 最小示例：`crates/c05_threads/tests/loom_minimal.rs`
  - 使用：`cargo test -p c05_threads --test loom_minimal`
- 适用范围：`c05_threads`、`c06_async`、`c20_distributed` 等
