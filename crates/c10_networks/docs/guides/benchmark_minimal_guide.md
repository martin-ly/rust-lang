# 网络最小基准指南（c10_networks）

> 适用范围：面向 `c10_networks` 示例与组件的最小可重复网络基准；适配 Windows/Linux/macOS。

## 📋 目录

- [网络最小基准指南（c10\_networks）](#网络最小基准指南c10_networks)
  - [📋 目录](#-目录)
  - [目的](#目的)
  - [前置](#前置)
  - [干跑与构建](#干跑与构建)
  - [运行](#运行)
  - [建议观测](#建议观测)
  - [关联](#关联)
  - [注意事项（建议）](#注意事项建议)

## 目的

- 为网络示例/服务提供最小化、可复制的基准步骤与建议参数。

## 前置

- Windows：以管理员运行 PowerShell 以便抓包/原始套接字（如需）。
- 可选优化：`$env:RUSTFLAGS = "-C target-cpu=native"`。
- 固定 CPU 频率/电源策略，关闭后台程序与自动更新。

## 干跑与构建

```powershell
cd .\crates\c10_networks
cargo bench --no-run | cat
```

## 运行

```powershell
# 如本 crate 的 benches 后续补充，可直接运行：
# cargo bench -p c10_networks | cat

# 先使用异步基准作为对照：
cargo bench -p c06_async | cat
```

## 建议观测

- 吞吐、连接建立时间、请求-响应延迟 p50/p95/p99。
- CPU/上下文切换、内存峰值、网络带宽与丢包率。
- DNS 解析延迟/命中率（与 `c10_networks::protocol::dns` 集成时）。

## 关联

- 最小基准总指南：`../../rust-formal-engineering-system/02_programming_paradigms/11_benchmark_minimal_guide.md`
- 异步基准：`../../c06_async/benches/`
- 同步/并行基准：`../../c05_threads/benches/`

## 注意事项（建议）

- 固定环境：关闭无关后台程序，固定 CPU 频率/电源策略，尽量在相同网络条件下对比。
- 重复次数：每组基准至少重复 5 次，记录 p50/p95/p99，剔除首个预热样本。
- 结果记录模板：

```text
case: <name>
env: <cpu/mem/os/net>
cmd: <exact command>
p50: <ms>  p95: <ms>  p99: <ms>
throughput: <req/s>  cpu: <%>  mem_peak: <MB>
notes: <anomalies/observations>
```
