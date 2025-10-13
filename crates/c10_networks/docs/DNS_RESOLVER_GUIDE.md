# DNS 解析器指南

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`STYLE.md`](STYLE.md)。

## 📋 目录

- [DNS 解析器指南](#dns-解析器指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [主要特性](#主要特性)
  - [⚡ 快速开始](#-快速开始)
    - [基础DNS查询](#基础dns查询)
    - [运行示例](#运行示例)
  - [🔧 基础用法](#-基础用法)
    - [创建DNS解析器](#创建dns解析器)
    - [查询不同类型记录](#查询不同类型记录)
    - [批量查询](#批量查询)
  - [🌐 系统DNS配置](#-系统dns配置)
    - [自动读取系统配置](#自动读取系统配置)
    - [手动配置DNS服务器](#手动配置dns服务器)
    - [跨平台系统配置](#跨平台系统配置)
  - [🔒 DoT/DoH 支持](#-dotdoh-支持)
    - [DoT (DNS over TLS) 配置](#dot-dns-over-tls-配置)
    - [DoH (DNS over HTTPS) 配置](#doh-dns-over-https-配置)
    - [多协议回退](#多协议回退)
  - [📊 高级特性](#-高级特性)
    - [DNS缓存](#dns缓存)
    - [自定义记录类型](#自定义记录类型)
    - [DNS负载均衡](#dns负载均衡)
    - [DNS监控](#dns监控)
  - [⚙️ 配置选项](#️-配置选项)
    - [DnsConfig 完整配置](#dnsconfig-完整配置)
    - [环境变量配置](#环境变量配置)
  - [🔍 错误处理](#-错误处理)
    - [错误类型](#错误类型)
    - [重试机制](#重试机制)
  - [📈 性能优化](#-性能优化)
    - [并发查询](#并发查询)
    - [缓存优化](#缓存优化)
  - [🧪 测试示例](#-测试示例)
    - [单元测试](#单元测试)
    - [集成测试](#集成测试)
    - [性能测试](#性能测试)
  - [❓ 常见问题](#-常见问题)
    - [Q: 如何设置DNS超时？](#q-如何设置dns超时)
    - [Q: 如何启用DNS缓存？](#q-如何启用dns缓存)
    - [Q: 如何配置DoT/DoH？](#q-如何配置dotdoh)
    - [Q: 如何处理DNS查询失败？](#q-如何处理dns查询失败)
    - [Q: 如何优化DNS性能？](#q-如何优化dns性能)
    - [Q: 如何查询特定记录类型？](#q-如何查询特定记录类型)
    - [Q: 如何实现DNS负载均衡？](#q-如何实现dns负载均衡)
    - [Q: 如何监控DNS性能？](#q-如何监控dns性能)

## 🎯 概述

C10 Networks 提供了基于 Hickory-DNS 的完整DNS解析功能，支持系统DNS、DoT（DNS over TLS）和DoH（DNS over HTTPS）协议。

### 主要特性

- **系统DNS**: 自动读取系统DNS配置
- **DoT支持**: DNS over TLS加密传输
- **DoH支持**: DNS over HTTPS加密传输
- **多记录类型**: A、AAAA、MX、SRV、TXT、PTR等
- **缓存机制**: 高效的DNS缓存
- **异步解析**: 基于Tokio的高性能实现

## ⚡ 快速开始

### 基础DNS查询

```rust
use c10_networks::protocol::dns::{DnsResolver, presets};
use c10_networks::error::NetworkResult;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    // 使用系统DNS配置
    let resolver = DnsResolver::from_system().await?;
    
    // 查询A记录
    let ips = resolver.lookup_ips("example.com").await?;
    println!("example.com 的IP地址: {:?}", ips);
    
    // 查询TXT记录
    let txt_records = resolver.lookup_txt("example.com").await?;
    println!("TXT记录: {:?}", txt_records);
    
    // 使用Cloudflare DoH
    let (cfg, opts) = presets::cloudflare_doh();
    let doh_resolver = DnsResolver::from_config(cfg, opts).await?;
    
    let doh_ips = doh_resolver.lookup_ips("google.com").await?;
    println!("Google.com (DoH): {:?}", doh_ips);
    
    Ok(())
}
```

### 运行示例

```bash
cargo run --example dns_lookup -- example.com
cargo run --example dns_doh_dot -- example.com
```

## 🔧 基础用法

### 创建DNS解析器

```rust
use c10_networks::protocol::dns::{DnsResolver, DnsConfig, DnsOptions};

// 使用系统配置
let resolver = DnsResolver::from_system().await?;

// 使用自定义配置
let config = DnsConfig::new()
    .with_nameservers(vec!["8.8.8.8".parse()?, "1.1.1.1".parse()?])
    .with_search_domains(vec!["example.com".to_string()])
    .with_ndots(1);

let options = DnsOptions::new()
    .with_timeout(Duration::from_secs(5))
    .with_attempts(3)
    .with_cache_size(1024)
    .with_validate(false);

let resolver = DnsResolver::from_config(config, options).await?;
```

### 查询不同类型记录

```rust
use c10_networks::protocol::dns::DnsResolver;

async fn query_different_records() -> NetworkResult<()> {
    let resolver = DnsResolver::from_system().await?;
    
    // A记录查询
    let a_records = resolver.lookup_ips("example.com").await?;
    println!("A记录: {:?}", a_records);
    
    // MX记录查询
    let mx_records = resolver.lookup_mx("example.com").await?;
    println!("MX记录: {:?}", mx_records);
    
    // SRV记录查询
    let srv_records = resolver.lookup_srv("_http._tcp.example.com").await?;
    println!("SRV记录: {:?}", srv_records);
    
    // TXT记录查询
    let txt_records = resolver.lookup_txt("example.com").await?;
    println!("TXT记录: {:?}", txt_records);
    
    // PTR记录查询（反向DNS）
    let ptr_records = resolver.reverse_lookup("8.8.8.8".parse()?).await?;
    println!("PTR记录: {:?}", ptr_records);
    
    Ok(())
}
```

### 批量查询

```rust
use c10_networks::protocol::dns::DnsResolver;
use futures::future::join_all;

async fn batch_dns_queries() -> NetworkResult<()> {
    let resolver = DnsResolver::from_system().await?;
    
    let domains = vec![
        "example.com",
        "google.com",
        "github.com",
        "rust-lang.org",
    ];
    
    // 并发查询多个域名
    let futures: Vec<_> = domains
        .into_iter()
        .map(|domain| resolver.lookup_ips(domain))
        .collect();
    
    let results = join_all(futures).await;
    
    for (domain, result) in domains.iter().zip(results) {
        match result {
            Ok(ips) => println!("{}: {:?}", domain, ips),
            Err(e) => eprintln!("{}: 查询失败 - {}", domain, e),
        }
    }
    
    Ok(())
}
```

## 🌐 系统DNS配置

### 自动读取系统配置

```rust
use c10_networks::protocol::dns::DnsResolver;

async fn system_dns_example() -> NetworkResult<()> {
    // 自动读取系统DNS配置
    let resolver = DnsResolver::from_system().await?;
    
    // 查询域名
    let ips = resolver.lookup_ips("example.com").await?;
    println!("系统DNS解析结果: {:?}", ips);
    
    Ok(())
}
```

### 手动配置DNS服务器

```rust
use c10_networks::protocol::dns::{DnsResolver, DnsConfig, DnsOptions};
use std::net::{IpAddr, Ipv4Addr};

async fn manual_dns_config() -> NetworkResult<()> {
    // 创建自定义DNS配置
    let mut config = DnsConfig::new();
    
    // 添加DNS服务器
    config.add_nameserver("8.8.8.8".parse()?);
    config.add_nameserver("1.1.1.1".parse()?);
    config.add_nameserver("9.9.9.9".parse()?);
    
    // 添加搜索域
    config.add_search_domain("example.com".to_string());
    config.add_search_domain("local".to_string());
    
    // 设置ndots
    config.set_ndots(1);
    
    // 创建选项
    let options = DnsOptions::new()
        .with_timeout(Duration::from_secs(5))
        .with_attempts(2)
        .with_cache_size(512)
        .with_validate(false);
    
    // 创建解析器
    let resolver = DnsResolver::from_config(config, options).await?;
    
    // 使用解析器
    let ips = resolver.lookup_ips("example.com").await?;
    println!("自定义DNS解析结果: {:?}", ips);
    
    Ok(())
}
```

### 跨平台系统配置

```rust
use c10_networks::protocol::dns::{DnsResolver, DnsConfig, DnsOptions};

async fn cross_platform_dns() -> NetworkResult<()> {
    let resolver = DnsResolver::from_system().await?;
    
    // 获取当前配置信息
    let config_info = resolver.get_config_info().await?;
    
    println!("DNS配置信息:");
    println!("  名称服务器: {:?}", config_info.nameservers);
    println!("  搜索域: {:?}", config_info.search_domains);
    println!("  ndots: {}", config_info.ndots);
    println!("  超时: {:?}", config_info.timeout);
    println!("  尝试次数: {}", config_info.attempts);
    
    Ok(())
}
```

## 🔒 DoT/DoH 支持

### DoT (DNS over TLS) 配置

```rust
use c10_networks::protocol::dns::{DnsResolver, presets};

async fn dot_example() -> NetworkResult<()> {
    // 使用Cloudflare DoT
    let (cfg, opts) = presets::cloudflare_dot();
    let dot_resolver = DnsResolver::from_config(cfg, opts).await?;
    
    // 查询域名
    let ips = dot_resolver.lookup_ips("example.com").await?;
    println!("DoT解析结果: {:?}", ips);
    
    Ok(())
}

async fn custom_dot_config() -> NetworkResult<()> {
    use c10_networks::protocol::dns::{DnsConfig, DnsOptions};
    use c10_networks::security::tls_reload::TlsConfig;
    
    // 自定义DoT配置
    let tls_config = TlsConfig::default()
        .with_verify_certificates(true)
        .with_verify_hostname(true)
        .with_sni("dns.google".to_string());
    
    let config = DnsConfig::new()
        .with_dot_server("8.8.8.8:853".parse()?)
        .with_tls_config(tls_config);
    
    let options = DnsOptions::new()
        .with_timeout(Duration::from_secs(10))
        .with_attempts(2);
    
    let resolver = DnsResolver::from_config(config, options).await?;
    
    let ips = resolver.lookup_ips("example.com").await?;
    println!("自定义DoT解析结果: {:?}", ips);
    
    Ok(())
}
```

### DoH (DNS over HTTPS) 配置

```rust
use c10_networks::protocol::dns::{DnsResolver, presets};

async fn doh_example() -> NetworkResult<()> {
    // 使用Cloudflare DoH
    let (cfg, opts) = presets::cloudflare_doh();
    let doh_resolver = DnsResolver::from_config(cfg, opts).await?;
    
    // 查询域名
    let ips = doh_resolver.lookup_ips("example.com").await?;
    println!("DoH解析结果: {:?}", ips);
    
    Ok(())
}

async fn custom_doh_config() -> NetworkResult<()> {
    use c10_networks::protocol::dns::{DnsConfig, DnsOptions};
    use c10_networks::security::tls_reload::TlsConfig;
    
    // 自定义DoH配置
    let tls_config = TlsConfig::default()
        .with_verify_certificates(true)
        .with_verify_hostname(true);
    
    let config = DnsConfig::new()
        .with_doh_endpoint("https://dns.google/dns-query".to_string())
        .with_tls_config(tls_config);
    
    let options = DnsOptions::new()
        .with_timeout(Duration::from_secs(10))
        .with_attempts(2);
    
    let resolver = DnsResolver::from_config(config, options).await?;
    
    let ips = resolver.lookup_ips("example.com").await?;
    println!("自定义DoH解析结果: {:?}", ips);
    
    Ok(())
}
```

### 多协议回退

```rust
use c10_networks::protocol::dns::{DnsResolver, presets};

async fn multi_protocol_fallback() -> NetworkResult<()> {
    let domain = "example.com";
    
    // 尝试不同的解析方式
    let resolvers = vec![
        ("系统DNS", DnsResolver::from_system().await?),
        ("Cloudflare DoH", {
            let (cfg, opts) = presets::cloudflare_doh();
            DnsResolver::from_config(cfg, opts).await?
        }),
        ("Google DoH", {
            let (cfg, opts) = presets::google_doh();
            DnsResolver::from_config(cfg, opts).await?
        }),
        ("Cloudflare DoT", {
            let (cfg, opts) = presets::cloudflare_dot();
            DnsResolver::from_config(cfg, opts).await?
        }),
    ];
    
    for (name, resolver) in resolvers {
        match resolver.lookup_ips(domain).await {
            Ok(ips) => {
                println!("{} 解析成功: {:?}", name, ips);
                break; // 第一个成功的解析器
            }
            Err(e) => {
                eprintln!("{} 解析失败: {}", name, e);
            }
        }
    }
    
    Ok(())
}
```

## 📊 高级特性

### DNS缓存

```rust
use c10_networks::protocol::dns::{DnsResolver, DnsOptions};
use std::time::Duration;

async fn dns_cache_example() -> NetworkResult<()> {
    // 启用缓存
    let options = DnsOptions::new()
        .with_cache_size(1024)
        .with_cache_ttl(Duration::from_secs(300)) // 5分钟
        .with_negative_cache_ttl(Duration::from_secs(60)); // 1分钟
    
    let resolver = DnsResolver::from_system().await?;
    
    // 第一次查询（从DNS服务器获取）
    let start = std::time::Instant::now();
    let ips1 = resolver.lookup_ips("example.com").await?;
    let duration1 = start.elapsed();
    
    // 第二次查询（从缓存获取）
    let start = std::time::Instant::now();
    let ips2 = resolver.lookup_ips("example.com").await?;
    let duration2 = start.elapsed();
    
    println!("第一次查询耗时: {:?}", duration1);
    println!("第二次查询耗时: {:?}", duration2);
    println!("缓存加速: {:.2}x", duration1.as_secs_f64() / duration2.as_secs_f64());
    
    assert_eq!(ips1, ips2);
    
    Ok(())
}
```

### 自定义记录类型

```rust
use c10_networks::protocol::dns::{DnsResolver, RecordType};

async fn custom_record_types() -> NetworkResult<()> {
    let resolver = DnsResolver::from_system().await?;
    
    // 查询自定义记录类型
    let records = resolver.lookup_records("example.com", RecordType::A).await?;
    println!("A记录: {:?}", records);
    
    let records = resolver.lookup_records("example.com", RecordType::AAAA).await?;
    println!("AAAA记录: {:?}", records);
    
    let records = resolver.lookup_records("example.com", RecordType::MX).await?;
    println!("MX记录: {:?}", records);
    
    let records = resolver.lookup_records("example.com", RecordType::TXT).await?;
    println!("TXT记录: {:?}", records);
    
    Ok(())
}
```

### DNS负载均衡

```rust
use c10_networks::protocol::dns::{DnsResolver, DnsConfig, DnsOptions};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;

struct DnsLoadBalancer {
    resolvers: Vec<DnsResolver>,
    current_index: Arc<Mutex<usize>>,
    stats: Arc<Mutex<HashMap<usize, u64>>>,
}

impl DnsLoadBalancer {
    fn new(resolvers: Vec<DnsResolver>) -> Self {
        Self {
            resolvers,
            current_index: Arc::new(Mutex::new(0)),
            stats: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    async fn resolve(&self, domain: &str) -> NetworkResult<Vec<std::net::IpAddr>> {
        let mut index = self.current_index.lock().await;
        let resolver_index = *index;
        
        // 轮询选择解析器
        *index = (*index + 1) % self.resolvers.len();
        drop(index);
        
        // 使用选中的解析器
        let resolver = &self.resolvers[resolver_index];
        let result = resolver.lookup_ips(domain).await;
        
        // 更新统计信息
        {
            let mut stats = self.stats.lock().await;
            *stats.entry(resolver_index).or_insert(0) += 1;
        }
        
        result
    }
    
    async fn get_stats(&self) -> HashMap<usize, u64> {
        let stats = self.stats.lock().await;
        stats.clone()
    }
}

async fn dns_load_balancer_example() -> NetworkResult<()> {
    // 创建多个解析器
    let resolvers = vec![
        DnsResolver::from_system().await?,
        {
            let (cfg, opts) = presets::cloudflare_doh();
            DnsResolver::from_config(cfg, opts).await?
        },
        {
            let (cfg, opts) = presets::google_doh();
            DnsResolver::from_config(cfg, opts).await?
        },
    ];
    
    let load_balancer = DnsLoadBalancer::new(resolvers);
    
    // 并发查询多个域名
    let domains = vec![
        "example.com",
        "google.com",
        "github.com",
        "rust-lang.org",
    ];
    
    let futures: Vec<_> = domains
        .into_iter()
        .map(|domain| load_balancer.resolve(domain))
        .collect();
    
    let results = futures::future::join_all(futures).await;
    
    for (domain, result) in domains.iter().zip(results) {
        match result {
            Ok(ips) => println!("{}: {:?}", domain, ips),
            Err(e) => eprintln!("{}: 查询失败 - {}", domain, e),
        }
    }
    
    // 显示负载均衡统计
    let stats = load_balancer.get_stats().await;
    println!("负载均衡统计: {:?}", stats);
    
    Ok(())
}
```

### DNS监控

```rust
use c10_networks::protocol::dns::{DnsResolver, DnsMonitor};
use std::time::Duration;

async fn dns_monitoring_example() -> NetworkResult<()> {
    let resolver = DnsResolver::from_system().await?;
    let monitor = DnsMonitor::new();
    
    // 注册监控
    let resolver_id = monitor.register_resolver(&resolver).await?;
    
    // 执行查询
    let start = std::time::Instant::now();
    let ips = resolver.lookup_ips("example.com").await?;
    let duration = start.elapsed();
    
    // 获取监控统计
    let stats = monitor.get_stats(resolver_id).await?;
    
    println!("查询结果: {:?}", ips);
    println!("查询耗时: {:?}", duration);
    println!("监控统计: {:?}", stats);
    
    // 检查DNS服务器健康状态
    let health = monitor.check_health(resolver_id).await?;
    println!("DNS服务器健康状态: {:?}", health);
    
    Ok(())
}
```

## ⚙️ 配置选项

### DnsConfig 完整配置

```rust
use c10_networks::protocol::dns::{DnsResolver, DnsConfig, DnsOptions};
use c10_networks::security::tls_reload::TlsConfig;
use std::time::Duration;

let config = DnsConfig::new()
    // 名称服务器
    .with_nameservers(vec![
        "8.8.8.8".parse()?,
        "1.1.1.1".parse()?,
        "9.9.9.9".parse()?,
    ])
    
    // 搜索域
    .with_search_domains(vec![
        "example.com".to_string(),
        "local".to_string(),
    ])
    
    // ndots设置
    .with_ndots(1)
    
    // DoT配置
    .with_dot_server("8.8.8.8:853".parse()?)
    .with_dot_sni("dns.google".to_string())
    
    // DoH配置
    .with_doh_endpoint("https://dns.google/dns-query".to_string())
    
    // TLS配置
    .with_tls_config(TlsConfig::default()
        .with_verify_certificates(true)
        .with_verify_hostname(true));

let options = DnsOptions::new()
    // 超时设置
    .with_timeout(Duration::from_secs(5))
    .with_connection_timeout(Duration::from_secs(10))
    
    // 重试设置
    .with_attempts(3)
    .with_retry_delay(Duration::from_millis(100))
    
    // 缓存设置
    .with_cache_size(1024)
    .with_cache_ttl(Duration::from_secs(300))
    .with_negative_cache_ttl(Duration::from_secs(60))
    
    // 其他选项
    .with_validate(false)
    .with_edns0(true)
    .with_dnssec(false);

let resolver = DnsResolver::from_config(config, options).await?;
```

### 环境变量配置

```bash
# DNS配置
export C10_DNS_TIMEOUT=5000
export C10_DNS_ATTEMPTS=3
export C10_DNS_CACHE_SIZE=1024
export C10_DNS_CACHE_TTL=300
export C10_DNS_NEGATIVE_CACHE_TTL=60
export C10_DNS_VALIDATE=false
export C10_DNS_EDNS0=true
export C10_DNS_DNSSEC=false

# DoT配置
export C10_DNS_DOT_SERVER=8.8.8.8:853
export C10_DNS_DOT_SNI=dns.google
export C10_DNS_DOT_VERIFY_CERTIFICATES=true
export C10_DNS_DOT_VERIFY_HOSTNAME=true

# DoH配置
export C10_DNS_DOH_ENDPOINT=https://dns.google/dns-query
export C10_DNS_DOH_VERIFY_CERTIFICATES=true
export C10_DNS_DOH_VERIFY_HOSTNAME=true
```

## 🔍 错误处理

### 错误类型

```rust
use c10_networks::error::{NetworkError, NetworkResult};

async fn handle_dns_errors() -> NetworkResult<()> {
    let resolver = DnsResolver::from_system().await?;
    
    match resolver.lookup_ips("nonexistent.example.invalid").await {
        Ok(ips) => {
            println!("查询成功: {:?}", ips);
        }
        Err(NetworkError::DnsError(dns_error)) => {
            match dns_error {
                DnsError::NameNotFound => {
                    println!("域名不存在");
                }
                DnsError::NoSuchDomain => {
                    println!("域名不存在");
                }
                DnsError::Timeout => {
                    println!("DNS查询超时");
                }
                DnsError::ServFail => {
                    println!("DNS服务器错误");
                }
                DnsError::Refused => {
                    println!("DNS查询被拒绝");
                }
                _ => {
                    eprintln!("DNS错误: {}", dns_error);
                }
            }
        }
        Err(e) => {
            eprintln!("其他错误: {}", e);
        }
    }
    
    Ok(())
}
```

### 重试机制

```rust
use c10_networks::protocol::dns::DnsResolver;
use std::time::Duration;

async fn dns_retry_example() -> NetworkResult<()> {
    let resolver = DnsResolver::from_system().await?;
    let domain = "example.com";
    let max_retries = 3;
    let retry_delay = Duration::from_millis(100);
    
    for attempt in 1..=max_retries {
        match resolver.lookup_ips(domain).await {
            Ok(ips) => {
                println!("查询成功 (尝试 {}): {:?}", attempt, ips);
                return Ok(());
            }
            Err(e) => {
                eprintln!("查询失败 (尝试 {}): {}", attempt, e);
                
                if attempt < max_retries {
                    println!("{}ms后重试...", retry_delay.as_millis());
                    tokio::time::sleep(retry_delay).await;
                } else {
                    return Err(e);
                }
            }
        }
    }
    
    Ok(())
}
```

## 📈 性能优化

### 并发查询

```rust
use c10_networks::protocol::dns::DnsResolver;
use futures::future::join_all;

async fn concurrent_dns_queries() -> NetworkResult<()> {
    let resolver = DnsResolver::from_system().await?;
    
    let domains = vec![
        "example.com",
        "google.com",
        "github.com",
        "rust-lang.org",
        "mozilla.org",
    ];
    
    // 并发查询所有域名
    let start = std::time::Instant::now();
    let futures: Vec<_> = domains
        .into_iter()
        .map(|domain| resolver.lookup_ips(domain))
        .collect();
    
    let results = join_all(futures).await;
    let duration = start.elapsed();
    
    // 处理结果
    let mut success_count = 0;
    for (domain, result) in domains.iter().zip(results) {
        match result {
            Ok(ips) => {
                println!("{}: {:?}", domain, ips);
                success_count += 1;
            }
            Err(e) => {
                eprintln!("{}: 查询失败 - {}", domain, e);
            }
        }
    }
    
    println!("并发查询 {} 个域名耗时: {:?}", domains.len(), duration);
    println!("成功查询: {}/{}", success_count, domains.len());
    
    Ok(())
}
```

### 缓存优化

```rust
use c10_networks::protocol::dns::{DnsResolver, DnsOptions};
use std::time::Duration;

async fn cache_optimization_example() -> NetworkResult<()> {
    // 配置大缓存
    let options = DnsOptions::new()
        .with_cache_size(4096)
        .with_cache_ttl(Duration::from_secs(600)) // 10分钟
        .with_negative_cache_ttl(Duration::from_secs(300)); // 5分钟
    
    let resolver = DnsResolver::from_system().await?;
    
    // 预热缓存
    let warmup_domains = vec![
        "example.com",
        "google.com",
        "github.com",
        "rust-lang.org",
    ];
    
    println!("预热DNS缓存...");
    for domain in &warmup_domains {
        let _ = resolver.lookup_ips(domain).await;
    }
    
    // 测试缓存性能
    let test_count = 1000;
    let start = std::time::Instant::now();
    
    for _ in 0..test_count {
        for domain in &warmup_domains {
            let _ = resolver.lookup_ips(domain).await;
        }
    }
    
    let duration = start.elapsed();
    let total_queries = test_count * warmup_domains.len();
    let queries_per_second = total_queries as f64 / duration.as_secs_f64();
    
    println!("缓存性能测试:");
    println!("  总查询数: {}", total_queries);
    println!("  总耗时: {:?}", duration);
    println!("  查询速度: {:.2} 查询/秒", queries_per_second);
    
    Ok(())
}
```

## 🧪 测试示例

### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use c10_networks::protocol::dns::{DnsResolver, presets};

    #[tokio::test]
    async fn test_dns_resolver_creation() {
        let resolver = DnsResolver::from_system().await.unwrap();
        assert!(resolver.is_configured());
    }

    #[tokio::test]
    async fn test_dns_a_record_query() {
        let resolver = DnsResolver::from_system().await.unwrap();
        let ips = resolver.lookup_ips("example.com").await.unwrap();
        
        assert!(!ips.is_empty());
        for ip in ips {
            assert!(ip.is_ipv4() || ip.is_ipv6());
        }
    }

    #[tokio::test]
    async fn test_dns_txt_record_query() {
        let resolver = DnsResolver::from_system().await.unwrap();
        let txt_records = resolver.lookup_txt("example.com").await.unwrap();
        
        // TXT记录可能为空，这是正常的
        for record in txt_records {
            assert!(!record.is_empty());
        }
    }

    #[tokio::test]
    async fn test_dns_mx_record_query() {
        let resolver = DnsResolver::from_system().await.unwrap();
        let mx_records = resolver.lookup_mx("example.com").await.unwrap();
        
        assert!(!mx_records.is_empty());
        for (priority, exchange) in mx_records {
            assert!(priority >= 0);
            assert!(!exchange.is_empty());
        }
    }

    #[tokio::test]
    async fn test_dns_reverse_lookup() {
        let resolver = DnsResolver::from_system().await.unwrap();
        let names = resolver.reverse_lookup("8.8.8.8".parse().unwrap()).await.unwrap();
        
        // 反向DNS查询可能失败，这是正常的
        for name in names {
            assert!(!name.is_empty());
        }
    }

    #[tokio::test]
    async fn test_doh_resolver() {
        let (cfg, opts) = presets::cloudflare_doh();
        let resolver = DnsResolver::from_config(cfg, opts).await.unwrap();
        
        let ips = resolver.lookup_ips("example.com").await.unwrap();
        assert!(!ips.is_empty());
    }

    #[tokio::test]
    async fn test_dot_resolver() {
        let (cfg, opts) = presets::cloudflare_dot();
        let resolver = DnsResolver::from_config(cfg, opts).await.unwrap();
        
        let ips = resolver.lookup_ips("example.com").await.unwrap();
        assert!(!ips.is_empty());
    }

    #[tokio::test]
    async fn test_dns_error_handling() {
        let resolver = DnsResolver::from_system().await.unwrap();
        
        // 查询不存在的域名
        let result = resolver.lookup_ips("nonexistent.example.invalid").await;
        assert!(result.is_err());
    }
}
```

### 集成测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;
    use c10_networks::protocol::dns::{DnsResolver, presets};

    #[tokio::test]
    async fn test_dns_resolver_comparison() {
        // 系统DNS
        let system_resolver = DnsResolver::from_system().await.unwrap();
        
        // Cloudflare DoH
        let (doh_cfg, doh_opts) = presets::cloudflare_doh();
        let doh_resolver = DnsResolver::from_config(doh_cfg, doh_opts).await.unwrap();
        
        // Cloudflare DoT
        let (dot_cfg, dot_opts) = presets::cloudflare_dot();
        let dot_resolver = DnsResolver::from_config(dot_cfg, dot_opts).await.unwrap();
        
        let domain = "example.com";
        
        // 查询同一个域名
        let system_ips = system_resolver.lookup_ips(domain).await.unwrap();
        let doh_ips = doh_resolver.lookup_ips(domain).await.unwrap();
        let dot_ips = dot_resolver.lookup_ips(domain).await.unwrap();
        
        // 结果应该相似（可能有细微差别）
        assert!(!system_ips.is_empty());
        assert!(!doh_ips.is_empty());
        assert!(!dot_ips.is_empty());
        
        println!("系统DNS: {:?}", system_ips);
        println!("DoH: {:?}", doh_ips);
        println!("DoT: {:?}", dot_ips);
    }

    #[tokio::test]
    async fn test_dns_caching() {
        let resolver = DnsResolver::from_system().await.unwrap();
        let domain = "example.com";
        
        // 第一次查询
        let start1 = std::time::Instant::now();
        let ips1 = resolver.lookup_ips(domain).await.unwrap();
        let duration1 = start1.elapsed();
        
        // 第二次查询（应该使用缓存）
        let start2 = std::time::Instant::now();
        let ips2 = resolver.lookup_ips(domain).await.unwrap();
        let duration2 = start2.elapsed();
        
        // 结果应该相同
        assert_eq!(ips1, ips2);
        
        // 第二次查询应该更快（使用缓存）
        assert!(duration2 < duration1);
        
        println!("第一次查询耗时: {:?}", duration1);
        println!("第二次查询耗时: {:?}", duration2);
    }

    #[tokio::test]
    async fn test_dns_concurrent_queries() {
        let resolver = DnsResolver::from_system().await.unwrap();
        
        let domains = vec![
            "example.com",
            "google.com",
            "github.com",
            "rust-lang.org",
        ];
        
        // 并发查询
        let start = std::time::Instant::now();
        let futures: Vec<_> = domains
            .into_iter()
            .map(|domain| resolver.lookup_ips(domain))
            .collect();
        
        let results = futures::future::join_all(futures).await;
        let duration = start.elapsed();
        
        // 验证结果
        for (domain, result) in domains.iter().zip(results) {
            let ips = result.unwrap();
            assert!(!ips.is_empty());
            println!("{}: {:?}", domain, ips);
        }
        
        println!("并发查询 {} 个域名耗时: {:?}", domains.len(), duration);
    }
}
```

### 性能测试

```rust
#[cfg(test)]
mod performance_tests {
    use super::*;
    use c10_networks::protocol::dns::{DnsResolver, DnsOptions};
    use std::time::Duration;

    #[tokio::test]
    async fn test_dns_performance() {
        let resolver = DnsResolver::from_system().await.unwrap();
        let domain = "example.com";
        
        let query_count = 100;
        let start = std::time::Instant::now();
        
        for _ in 0..query_count {
            let _ = resolver.lookup_ips(domain).await.unwrap();
        }
        
        let duration = start.elapsed();
        let queries_per_second = query_count as f64 / duration.as_secs_f64();
        
        println!("DNS性能测试:");
        println!("  查询次数: {}", query_count);
        println!("  总耗时: {:?}", duration);
        println!("  查询速度: {:.2} 查询/秒", queries_per_second);
        
        // 断言性能要求
        assert!(queries_per_second > 10.0); // 至少10查询/秒
    }

    #[tokio::test]
    async fn test_dns_cache_performance() {
        let options = DnsOptions::new()
            .with_cache_size(1024)
            .with_cache_ttl(Duration::from_secs(300));
        
        let resolver = DnsResolver::from_system().await.unwrap();
        let domain = "example.com";
        
        // 预热缓存
        let _ = resolver.lookup_ips(domain).await.unwrap();
        
        // 测试缓存性能
        let query_count = 1000;
        let start = std::time::Instant::now();
        
        for _ in 0..query_count {
            let _ = resolver.lookup_ips(domain).await.unwrap();
        }
        
        let duration = start.elapsed();
        let queries_per_second = query_count as f64 / duration.as_secs_f64();
        
        println!("DNS缓存性能测试:");
        println!("  查询次数: {}", query_count);
        println!("  总耗时: {:?}", duration);
        println!("  查询速度: {:.2} 查询/秒", queries_per_second);
        
        // 缓存查询应该非常快
        assert!(queries_per_second > 1000.0); // 至少1000查询/秒
    }

    #[tokio::test]
    async fn test_dns_concurrent_performance() {
        let resolver = DnsResolver::from_system().await.unwrap();
        
        let domains = vec![
            "example.com",
            "google.com",
            "github.com",
            "rust-lang.org",
            "mozilla.org",
        ];
        
        let concurrent_count = 50;
        let start = std::time::Instant::now();
        
        let mut tasks = Vec::new();
        for _ in 0..concurrent_count {
            let resolver = resolver.clone();
            let domains = domains.clone();
            
            let task = tokio::spawn(async move {
                let mut total_queries = 0;
                for domain in domains {
                    let _ = resolver.lookup_ips(domain).await.unwrap();
                    total_queries += 1;
                }
                total_queries
            });
            
            tasks.push(task);
        }
        
        let results = futures::future::join_all(tasks).await;
        let duration = start.elapsed();
        
        let total_queries: usize = results.into_iter().map(|r| r.unwrap()).sum();
        let queries_per_second = total_queries as f64 / duration.as_secs_f64();
        
        println!("DNS并发性能测试:");
        println!("  并发任务数: {}", concurrent_count);
        println!("  总查询数: {}", total_queries);
        println!("  总耗时: {:?}", duration);
        println!("  查询速度: {:.2} 查询/秒", queries_per_second);
        
        // 断言性能要求
        assert!(queries_per_second > 50.0); // 至少50查询/秒
    }
}
```

## ❓ 常见问题

### Q: 如何设置DNS超时？

A: 使用 `DnsOptions::with_timeout()` 方法设置查询超时时间。

### Q: 如何启用DNS缓存？

A: 使用 `DnsOptions::with_cache_size()` 和 `with_cache_ttl()` 方法配置缓存。

### Q: 如何配置DoT/DoH？

A: 使用 `presets::cloudflare_dot()` 或 `presets::cloudflare_doh()` 预设配置。

### Q: 如何处理DNS查询失败？

A: 实现重试机制，或使用多个DNS服务器作为备选。

### Q: 如何优化DNS性能？

A: 启用缓存、使用并发查询、选择合适的DNS服务器。

### Q: 如何查询特定记录类型？

A: 使用 `lookup_records()` 方法指定记录类型。

### Q: 如何实现DNS负载均衡？

A: 使用多个DNS解析器，实现轮询或健康检查。

### Q: 如何监控DNS性能？

A: 使用 `DnsMonitor` 监控查询统计和服务器健康状态。

---

**DNS解析器指南完成！** 🎉

现在您已经掌握了C10 Networks DNS解析器的完整用法，可以构建高性能的域名解析应用程序了。

*最后更新: 2025年1月*  
*文档版本: v1.0*  
*维护者: C10 Networks 开发团队*
