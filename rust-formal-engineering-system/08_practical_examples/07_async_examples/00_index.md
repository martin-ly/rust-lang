# 异步示例（Async Examples）索引

## 示例清单（摘取）

- select/try_join/JoinSet 基础示例
- 分布式锁、流式处理、背压控制
- 窗口批处理与限速管道
- tracing 与 tokio-console 调试

## 最小可运行示例

- `cargo run -p c06_async --bin tokio_select_exp01`
- `cargo run -p c06_async --bin tokio_try_join_exp01`
- `cargo run -p c06_async --bin tokio_joinset_exp01`

## 常见问题与排错

- 运行时报错缺少 Tokio runtime：确认 `#[tokio::main]` 或在 main 中创建 runtime。
- 任务卡死：检查 `await` 前是否存在互相等待；添加超时/取消。
- 高延迟抖动：确认背压容量、限流参数与批大小设置。

## 运行

- 参见：`crates/c06_async/README.md` 与 `docs/run_guide.md`
- PowerShell 示例见对应 README 顶部导航

## 导航

- 返回实践示例：[`../00_index.md`](../00_index.md)
- 异步范式：[`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
