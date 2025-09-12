# 系统示例（System Examples）索引

## 主题

- 线程与并发：作用域线程、工作窃取、优先级/亲和性
- 无锁结构：环形缓冲、并发哈希表、队列
- 性能与剖析：bench、perf/pprof/WPA

## 最小可运行示例

- `cargo run -p c05_threads --example basic`
- `cargo run -p c05_threads --example priority_channels_demo`
- `cargo bench -p c05_threads`

## 常见问题与排错

- 基准波动：固定 CPU 亲和性、关闭后台程序、稳定电源策略。
- 数据竞争：优先使用作用域线程或无锁结构；仔细审视共享可变状态。
- NUMA 跨节点抖动：绑定内存与线程到同一 NUMA 节点。

## 运行

- 参见：`crates/c05_threads/README.md`
- `cargo run -p c05_threads --example <name>`

## 导航

- 返回实践示例：[`../00_index.md`](../00_index.md)
- 线程模块：[`../../../crates/c05_threads`](../../../crates/c05_threads/)
