# DNS 解析机制与 Hickory-DNS 集成指南（Rust 1.89）

本指南介绍 `c10_networks` 如何基于 Hickory-DNS（原 trust-dns）实现现代 DNS 解析，包括系统解析、DoT（DNS over TLS）、DoH（DNS over HTTPS）、常见记录查询与逆向解析，并给出最佳实践与性能/安全建议。

## 理论剖析：从域名到 IP 的旅程（1.1/1.2/1.3）

### 1.1 DNS 基础理论：从域名到 IP 的旅程

- 域名层级：`www.example.com.` 自右向左解析，根（`.`）→ 顶级域（`com`）→ 权威域（`example.com`）→ 具体主机名（`www`）。
- 解析角色：
  - **递归解析器（Resolver）**：通常由操作系统或 ISP 提供，负责替用户向外查询；Hickory 在本库中扮演该角色。
  - **权威服务器（Authoritative）**：负责返回最终记录（A/AAAA/MX/TXT/SRV 等）。
  - **根与 TLD 服务器**：提供权威服务器的“指路信息”。
- 缓存与 TTL：解析器会依据记录 TTL 进行缓存，降低延迟与上游压力；TTL 过期需刷新。
- 记录类型要点：
  - **A/AAAA**：IPv4/IPv6 地址；
  - **CNAME**：别名指向真实域名；
  - **MX**：邮件交换优先级与主机；
  - **SRV**：服务发现（端口、优先级、权重、目标主机）；
  - **PTR**：逆向解析，从 IP 到域名。

### 1.2 Rust 标准库 DNS 解析的局限性

- `std::net::ToSocketAddrs` 解析简单直观，但：
  - 不支持 DoT/DoH 等加密传输；
  - 配置能力有限（超时、重试、缓存、NameServer 列表等）；
  - 错误信息较粗粒度，难以诊断复杂网络问题；
  - 无法轻松查询 TXT/MX/SRV/PTR 等丰富记录类型。

### 1.3 Hickory-DNS 的引入：纯 Rust 的 DNS

- Hickory（trust-dns 延续）提供纯 Rust 的递归解析组件：
  - 支持系统配置读取（`system-config`）、DoT/DoH（`rustls`）、自定义 NameServer、缓存、细粒度选项；
  - 与 Tokio 生态良好兼容，异步高并发；
  - 错误类型更细分，方便区分“无记录”“超时”“网络错误”等场景，利于观测与退避策略。

## 1. 依赖

```toml
hickory-resolver = { version = "0.24", features = ["tokio-runtime", "system-config", "dns-over-https-rustls", "dns-over-tls-rustls"] }
hickory-proto = "0.24"
```

## 2. 快速开始

```rust
use c10_networks::protocol::dns::{DnsResolver, presets};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 系统解析器（/etc/resolv.conf、Windows 注册表等）
    let sys = DnsResolver::from_system().await?;
    let ips = sys.lookup_ips("example.com").await?;
    println!("A/AAAA => {:?}", ips);

    // Cloudflare DoH 解析器
    let (cfg, opts) = presets::cloudflare_doh();
    let doh = DnsResolver::from_config(cfg, opts).await?;
    let txt = doh.lookup_txt("example.com").await?;
    println!("TXT => {:?}", txt);
    Ok(())
}
```

## 基本 DNS 解析实例：规避启动错误

常见启动期问题与规避手段：

- 启动在没有 Tokio Runtime 的上下文中调用异步解析：确保 `#[tokio::main]` 或显式创建 Runtime。
- 系统配置不可用（容器极简镜像/裁剪环境）：优先尝试 `from_system()`，失败时自动回退到 DoH 预设（Cloudflare/Google）。
- 解析超时导致进程卡顿：设置合理超时与尝试次数，并在启动路径只做“健康检查级”解析。

示例（带超时与回退）：

```rust
use c10_networks::protocol::dns::{DnsResolver, presets};
use std::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 优先系统解析器，失败再回退到 Cloudflare DoH
    let resolver = match DnsResolver::from_system().await {
        Ok(r) => r,
        Err(_) => {
            let (cfg, mut opts) = presets::cloudflare_doh();
            opts.timeout = Some(Duration::from_millis(3000));
            DnsResolver::from_config(cfg, opts).await?
        }
    };

    // 启动期仅做关键域名的轻量检查，避免阻塞主路径
    let _ = resolver.lookup_ips("example.com").await; // 忽略失败，交给后续重试与观测
    Ok(())
}
```

要点：

- 启动期不因单次解析失败而崩溃；
- 在业务路径结合重试/缓存，避免反复触发外部查询；
- 通过 `RUST_LOG` + `tracing_subscriber` 记录耗时/错误，便于快速定位。

## 高级配置：自定义 NameServer 以高效解决错误

当系统 DNS/公共 DoH 不稳定或需要内网权威时，可手动指定 NameServer：

```rust
use c10_networks::protocol::dns::DnsResolver;
use hickory_resolver::config::{ResolverConfig, ResolverOpts, NameServerConfig, NameServerConfigGroup, Protocol};
use std::net::{IpAddr, Ipv4Addr, SocketAddr};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 自定义 NameServer 列表（例如：内网权威 + 公网备用）
    let mut group = NameServerConfigGroup::with_capacity(2);
    group.push(NameServerConfig::new(
        SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 0, 0, 53)), 53),
        Protocol::Udp,
    ));
    group.push(NameServerConfig::new(
        SocketAddr::new(IpAddr::V4(Ipv4Addr::new(1, 1, 1, 1)), 53),
        Protocol::Udp,
    ));

    let mut cfg = ResolverConfig::from_parts(None, vec![], group);
    let mut opts = ResolverOpts::default();
    // 调整关键参数：
    opts.attempts = 2;           // 每个服务器尝试次数
    opts.cache_size = 1024;      // 进程内缓存容量
    opts.validate = false;       // 是否启用 DNSSEC 验证（如需）
    opts.timeout = std::time::Duration::from_millis(2500);

    let resolver = DnsResolver::from_config(cfg, opts).await?;
    let addrs = resolver.lookup_ips("internal.service.local").await?;
    println!("internal => {:?}", addrs);
    Ok(())
}
```

进一步：

- DoT（853/TCP）示例：将 `Protocol::Tls` 与相应 SNI/证书校验配好（参考下文预设与 `rustls`）。
- DoH：优先使用预设生成器（如 `presets::cloudflare_doh()`），或自行构造 HTTPS 端点与 `rustls` 根证书。
- 在容器/边缘环境中，优先选择接入点最近、丢包率低的 NameServer，并缩短超时、增加并行度以降低尾延迟。

## 3. API 一览

- `from_system()`：使用系统 DNS 配置创建解析器
- `from_config(config, opts)`：自定义解析器（可指向 DoT/DoH）
- `lookup_ips(host)`：查询并合并 A 与 AAAA
- `lookup_txt(name)`：查询 TXT
- `lookup_mx(name)`：查询 MX，返回 `(preference, exchange)`
- `lookup_srv(name)`：查询 SRV，返回 `(SRV, target)`
- `reverse_lookup(ip)`：PTR 逆向解析
- `resolve_socket_addrs(host, port)`：域名解析为 `SocketAddr` 列表

## 4. 预设解析器

模块 `presets` 提供：

- `cloudflare_doh()`：`https://cloudflare-dns.com/dns-query`
- `cloudflare_dot()`：`1.1.1.1:853`，SNI: `cloudflare-dns.com`
- `google_doh()`：`https://dns.google/dns-query`
- `google_dot()`：`8.8.8.8:853`，SNI: `dns.google`
- `quad9_doh()`：`https://dns.quad9.net/dns-query`
- `quad9_dot()`：`9.9.9.9:853`，SNI: `dns.quad9.net`

你可以用相同方式定义其它 DoH/DoT 服务器。

## 5. 最佳实践

- 超时与重试：结合 `diagnostics::NetDiagnostics::retry_with_backoff` 做重试
- 首选系统解析，再按需切换到可信 DoH/DoT 提升隐私与一致性
- 业务路径建议缓存解析结果（如 `performance::cache`）以降低延迟
- 解析失败优先区分：无记录、超时、网络错误，日志清晰化

## 6. 安全建议

- 生产环境优先使用 DoT/DoH，避免明文 DNS 泄露
- 配置 SNI 与证书校验（本库依赖 `rustls` 路径）
- 网络受限环境下准备降级路径与合理超时

## 7. 调试技巧

- 开启 `tracing_subscriber` 查看解析耗时与错误
- 使用 `reverse_lookup` 对可疑 IP 做 PTR 检查
- 结合 `c07_process` 的抓包/超时示例定位网络中断

## 8. 示例与测试

- 示例：`examples/dns_lookup.rs`
- 示例：`examples/unified_dns.rs`（通过 `unified_api::NetClient` 统一入口，支持 `C10_DNS_BACKEND` 切换解析器）
- 示例：`examples/dns_doh_dot.rs`（DoH→DoT→System 级联回退）
- 示例：`examples/dns_custom_ns.rs`（自定义 NameServer 列表与超时/重试）
- 示例：`examples/dns_records.rs`（MX/SRV/TXT 综合查询）
- 示例：`examples/dns_ptr.rs`（逆向解析 PTR）
- 示例：`examples/dns_negative_cache.rs`（成功/失败短期负缓存演示）
- 测试：`tests/dns_tests.rs`（需外网，可通过 `C10_SKIP_NETWORK_TESTS=1` 跳过）

### 环境变量

- `C10_DNS_BACKEND`：`system|cloudflare_doh|cloudflare_dot|google_doh|google_dot|quad9_doh|quad9_dot`
- `C10_DNS_TIMEOUT_MS`：解析超时（毫秒，默认 5000）
- `C10_DNS_ATTEMPTS`：解析尝试次数（默认 2）
- `C10_DNS_CACHE_SIZE`：进程内 DNS 缓存条目上限（默认 512）
- `C10_DNS_CACHE_TTL_MS`：DNS 缓存 TTL（毫秒，默认 60000）

### 一键运行脚本（可选）

- Windows（PowerShell）：`scripts/run_examples.ps1 -Domain example.com -SkipNetTests`
- Bash：`scripts/run_examples.sh example.com`（如需跳过外网测试：`export C10_SKIP_NETWORK_TESTS=1`）

统一入口（`unified_api::NetClient`）默认策略：

- 使用进程内缓存（可通过上述 TTL/Size 配置）
- 失败回退顺序：当前解析器 → Cloudflare DoH → Google DoH

## 9. 迁移自 trust-dns

`hickory-*` 为 trust-dns 的延续，API 兼容性总体友好。注意选择 `tokio-runtime` 与对应的 DoT/DoH feature。

---

若你需要企业内网 DNS、EDNS、DNSSEC 等高级特性，请在 issue 中反馈使用场景以便扩展支持。

## 10. 错误分类与排查流程

- 常见错误分类：
  - **NameNotFound/RecordNotFound**：域名存在但无对应记录类型；
  - **NoSuchDomain (NXDOMAIN)**：域名不存在；
  - **Timeout**：上游无响应或网络拥塞；
  - **ServFail**：上游服务异常（递归/权威）；
  - **Proto/Decode**：报文解析错误或不兼容扩展；
  - **Tls/Http（DoT/DoH）**：证书、SNI、握手、HTTP 传输问题。
- 排查建议：
  - 使用 `reverse_lookup` 验证可疑 IP；
  - 切换到 DoH 预设排除本地 DNS 问题；
  - 降低超时并增加并行度（多 NameServer）定位尾延迟；
  - 通过 `tracing` 采样关键域名查询耗时与失败率；
  - 在容器内添加 `iputils`/`curl` 等排查基础工具。

## 11. 超时、重试与并发查询策略

- 建议：
  - **启动期**：短超时（2-3s）+ 少量尝试（1-2 次），避免阻塞；
  - **业务路径**：指数退避重试（2-3 次），失败降级到备用解析器；
  - **多上游并发**：对多个 NameServer 并发首响应优先，降低尾延迟；
  - **连接复用**：DoH/DoT 在长连接场景中延迟更稳定。
- 指数退避示意：

```rust
use std::time::Duration;
use tokio::time::sleep;

async fn retry_with_backoff<F, Fut, T, E>(mut f: F) -> Result<T, E>
where
    F: FnMut() -> Fut,
    Fut: std::future::Future<Output = Result<T, E>>,
{
    let mut delay = Duration::from_millis(200);
    for _ in 0..3 {
        match f().await {
            Ok(v) => return Ok(v),
            Err(_) => sleep(delay).await,
        }
        delay = delay.saturating_mul(2);
    }
    f().await
}
```

## 12. 缓存策略与一致性

- 建议开启进程内缓存并尊重 TTL；对强一致需求的关键域名可设置较短 TTL；
- 对热点域名引入应用侧只读缓存（秒级），减少抖动；
- 缓存穿透与击穿：对频繁失败的域名可短暂缓存失败（负缓存）以保护上游；
- 灰度发布中，谨慎使用长 TTL，避免流量偏斜与回滚困难。

## 13. DoT/DoH 配置细节与证书校验

- 推荐优先使用文档中的 `presets::*` 预设，它们已包含正确的端口、SNI 与 `rustls` 校验路径；
- 若需自定义：
  - DoT：确保目的端口 853，配置正确的 SNI（与目标证书一致），并启用证书校验；
  - DoH：确保 `https://.../dns-query` 端点可达，HTTP/2 连接复用可显著降低延迟；
  - 受限环境可预置根证书或证书固定（pinning），注意更新策略与轮换；
  - 代理场景：DoH 可复用现有 HTTPS 代理通道，减少放通规则复杂度。

## 14. 跨平台系统配置说明

- Linux：读取 `/etc/resolv.conf`，可能包含 `search` 后缀与多个 `nameserver`；
- macOS：使用系统 API；
- Windows：读取注册表/系统配置，注意企业域环境下的自定义策略（如 split-horizon）；
- 容器/最小化系统：系统配置可能缺失，建议直接使用 DoH 预设或自定义 NameServer。

## 15. 更多示例

### 15.1 逆向解析（PTR）

```rust
use c10_networks::protocol::dns::DnsResolver;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let r = DnsResolver::from_system().await?;
    let names = r.reverse_lookup("1.1.1.1".parse()?).await?;
    println!("PTR => {:?}", names);
    Ok(())
}
```

### 15.2 MX/SRV/TXT 查询

```rust
use c10_networks::protocol::dns::DnsResolver;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let r = DnsResolver::from_system().await?;
    let mx = r.lookup_mx("example.com").await?;
    println!("MX => {:?}", mx);
    let srv = r.lookup_srv("_xmpp-server._tcp.example.com").await?;
    println!("SRV => {:?}", srv);
    let txt = r.lookup_txt("example.com").await?;
    println!("TXT => {:?}", txt);
    Ok(())
}
```

### 15.3 将域名解析为 SocketAddr

```rust
use c10_networks::protocol::dns::DnsResolver;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let r = DnsResolver::from_system().await?;
    let addrs = r.resolve_socket_addrs("example.com", 443).await?;
    for a in addrs { println!("{}", a); }
    Ok(())
}
```

## 16. 与统一入口（unified_api::NetClient）的集成

- 环境变量回顾：
  - `C10_DNS_BACKEND`：`system|cloudflare_doh|cloudflare_dot|google_doh|google_dot|quad9_doh|quad9_dot`
  - `C10_DNS_TIMEOUT_MS`、`C10_DNS_ATTEMPTS`、`C10_DNS_CACHE_SIZE`、`C10_DNS_CACHE_TTL_MS`
- 策略：
  - 统一入口默认启用缓存与失败回退（当前 → Cloudflare DoH → Google DoH）；
  - 对关键调用链路可在创建 `NetClient` 时注入自定义解析器实例；
  - 在高并发/短连接场景，优先选择 DoH/DoT 以提升隐私与一致性。

### 16.1 CI/测试策略与网络可选跳过

- 外网依赖测试在 CI 中应默认跳过，避免因网络波动导致不稳定：
  - 使用环境变量开关：`C10_SKIP_NETWORK_TESTS=1` 时跳过涉及外网的 DNS 测试；
  - 对示例运行与基准测试添加说明：需要外网时在本地手动运行；
  - 为关键路径提供本地桩（mock）或内网可控 NameServer；
- 建议：
  - 将少量连通性“冒烟测试”标记为非阻塞（optional），仅在夜间计划任务中运行；
  - 工具链缓存依赖，降低 CI 漂移；
  - 对 DoH/DoT 端点进行域名与 IP 双栈可用性监控。

## 17. 性能基准建议

- 指标：中位数/尾延迟（P50/P95/P99）、失败率、缓存命中率、上游查询次数；
- 维度：不同后端（system/DoH/DoT）、不同地区/网络、并发度、缓存开关；
- 方法：基于 Tokio 多任务并发发起固定样本查询，配合 `criterion`/自研基准脚本记录；
- 结论建议：
  - 本地稳定网络：系统解析 + 缓存通常最佳；
  - 跨网络/跨地区：DoH（就近 Anycast）+ 并发多上游更稳；
  - 长连服务：DoH/HTTP2 复用可显著降低尾延迟。

## 18. DNSSEC：完整性与来源认证

- 作用：通过数字签名链（DS、DNSKEY、RRSIG、NSEC/NSEC3）验证记录未被篡改，提升安全性；
- 代价：包体更大、解析耗时略增、需要可用的信任锚（根密钥）与校验链；
- 使用建议：
  - 公网安全敏感业务可启用验证；
  - 内网或强实时业务视权衡选择；
  - 结合缓存减少重复校验成本。
- 在 Hickory 中：
  - 配置项 `ResolverOpts.validate = true` 可启用验证（前提是上游支持并提供必要记录）；
  - 注意与 DoH/DoT 同时使用时的整体延迟影响与重试策略。

## 19. EDNS（扩展 DNS）与大包处理

- 作用：扩展 UDP 包体上限（典型 1232/4096 字节等）、携带额外选项（如 DNS Cookie），提升能力与抗攻击性；
- 风险：部分路径不兼容大包或被中间设备丢弃，导致超时；
- 建议：
  - 启用 EDNS 但保守设置最大 UDP 响应大小（如 1232），超大响应退回 TCP/DoT/DoH；
  - 遇到超时/丢包，降低上限或强制走 TCP/DoT/DoH；
  - 对关键查询开启并发多上游可降低兼容性问题带来的尾延迟。

## 20. 企业内网与 Split-Horizon（多视图）

- 现象：同一域名在内外网解析结果不同（如 `service.company.local` 内网解析到私网地址，外网不可见）；
- 建议：
  - 为内网服务优先配置权威内网 NameServer（如 AD DNS、CoreDNS），并置于自定义列表首位；
  - 对外网域名再配置 DoH/DoT 作为兜底；
  - 在容器/多集群：不同工作负载按命名空间或环境变量选择不同解析器实例；
  - 配合 `search` 后缀时，确保查询顺序与时间开销可控，避免无谓的 NXDOMAIN 放大。

## 21. GeoDNS 与全局负载均衡

- 目标：依据客户端地理位置/网络距离返回就近/最优地址，实现流量调度与容灾；
- 方式：
  - 基于权威侧（如托管 DNS 提供商）配置地理/ASN 策略；
  - 应用侧对多 IP 进行健康检查与优选（Happy Eyeballs、并行探测）；
  - TTL 策略配合：降低切换收敛时间，避免缓存过久导致流量固化；
  - 对 IPv6/IPv4 双栈优选，减少连接建立时间。

## 22. 安全加固与最小权限配置

- 原则：最小授权、最小暴露、可观测与快速撤回；
- 建议：
  - 优先 DoH/DoT，开启 SNI 与证书校验；
  - 生产环境使用受信 CA 或证书固定（pinning），避免自签名临时证书长时间在线；
  - 严格的超时与重试上限，避免放大攻击或资源耗尽；
  - 记录失败类别与上游地址，便于拉黑不稳定或异常的上游；
  - 内网权威仅对内暴露；分区（Zone）最小化、拆分读写；
  - 对管理接口启用多因素与变更审计，变更支持灰度发布与快速回滚。

### 22.1 DoT 的 SNI 与证书固定（Pinning）

- SNI：对 DoT 服务器（如 `1.1.1.1:853`）必须设置与证书匹配的 SNI（如 `cloudflare-dns.com`），否则握手可能失败；
- 证书固定：
  - 方式一：固定服务端证书公钥指纹（需跟踪轮换计划，适合受控环境）；
  - 方式二：固定根/中间 CA（更新周期较长，风险更低）；
  - 失败回退：若校验失败，立即回退到备用解析器（DoH 或系统），同时打点报警；
- 根证书：
  - 生产环境应使用系统或发行版提供的受信根集合；
  - 容器/最小系统可能缺失根证书，需随应用打包并定期更新。

### 22.2 Pinning 实操提示

- 建议仅对关键路径/高价值域名启用严格 pinning；
- 预留至少一个无需严格 pinning 的备用路径，以降低大面积故障风险；
- 记录证书链哈希与有效期，配合运维订阅到期提醒。
