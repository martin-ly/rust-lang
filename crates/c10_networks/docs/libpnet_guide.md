# libpnet 实战指南（C10 Networks）

> 适用范围：Rust 1.89+，Tokio 1.35+；Windows 需安装 Npcap；Linux 需 root 或 `CAP_NET_RAW`。

## 概览

- 抓包通道：基于 `pnet_datalink::channel` 的以太网帧捕获
- 协议解析：`pnet_packet::{ethernet, arp, ipv4, tcp}`
- 异步整合：Tokio + `spawn_blocking` + `mpsc` 实现抓包流水线
- 离线 PCAP：启用 `offline` feature 解析本地 `pcap`

## 环境准备（Windows）

1) 安装 Npcap（管理员，启用 WinPcap 兼容）
2) 安装 CMake、VS Build Tools（C++）、NASM（可选）
3) 确保未设置 `AWS_LC_SYS_NO_ASM=1`（或重开终端）
4) 以管理员运行 PowerShell 以便原始套接字/抓包

## Linux/macOS 注意事项

- Linux: 需要 `CAP_NET_RAW` 或 root 权限；可使用 `sudo` 运行
- macOS: 需安装 `libpcap`（通常自带）；第一次抓包可能触发权限弹窗
- 接口名差异：Linux 常见 `eth0`/`enp0s3`，macOS 常见 `en0`

## 同步 ARP 抓包

```rust
use c10_networks::sniff::{ArpSniffer, ArpSniffConfig};

let records = ArpSniffer::sniff_arp_sync(ArpSniffConfig { iface_name: None, promiscuous: true }, Some(10))?;
for r in records { println!("{:?}", r); }
```

## TCP 流量监控（一次性）

```rust
use c10_networks::sniff::monitor_tcp_once;
let rep = monitor_tcp_once(None, 5)?;
println!("total packets={} bytes={} in {:?}", rep.total.packets, rep.total.bytes, rep.duration);
```

## 异步流水线

```rust
use c10_networks::sniff::{arp_stream, tcp_stats_stream, ArpSniffConfig};
use std::time::Duration;

// ARP 异步
let mut rx = arp_stream(ArpSniffConfig::default(), 1024).await?;
while let Some(rec) = rx.recv().await { println!("ARP {:?} -> {:?}", rec.sender_ip, rec.target_ip); }

// TCP 周期统计
let mut rx2 = tcp_stats_stream(None, Duration::from_secs(2), 128).await?;
while let Some(snap) = rx2.recv().await { println!("TCP {} pkts {} bytes", snap.total.packets, snap.total.bytes); }
```

## 自定义 UDP 协议

```rust
use c10_networks::sniff::{UdpCustomMessage, udp_custom_roundtrip};
let msg = UdpCustomMessage { version: 1, msg_type: 1, payload: b"hi".to_vec() };
let resp = udp_custom_roundtrip("127.0.0.1:9000", &msg).await?;
println!("resp type={} len={}", resp.msg_type, resp.payload.len());
```

## 常见问题

- 权限不足导致抓不到包：以管理员运行 PowerShell；确认 Npcap 安装成功
- 构建时报 `Missing dependency: cmake`：安装 CMake/VS Build Tools；重开终端
- 没有任何包：指定正确接口名（如 `Ethernet`/`eth0`/`en0`），或确保该接口有实时流量

## 离线 PCAP 使用（feature = offline）

启用特性：`cargo run -p c10_networks --features offline --example ...`

```rust
use c10_networks::sniff::{parse_pcap_arp, parse_pcap_tcp_stats};

let arp = parse_pcap_arp("capture.pcap", Some(20))?;
let tcp = parse_pcap_tcp_stats("capture.pcap")?;
println!("arp_records={} tcp_packets={} tcp_bytes={}", arp.len(), tcp.packets, tcp.bytes);
```

## 关联与示例

- 示例：`examples/sniff_arp.rs`、`examples/monitor_tcp.rs`
- CI/权限：部分示例需要管理员/root；CI 中默认跳过依赖原始套接字的测试
