//! DNS 查询示例
//!
//! 这个示例展示了如何使用 c10_networks 库进行 DNS 查询
//!
//! ## 📖 理论基础
//!
//! DNS (域名系统) 是互联网的目录服务，将域名映射到 IP 地址：
//!
//! - **分层结构**: 树状域名空间
//! - **递归查询**: 客户端向 DNS 服务器查询
//! - **迭代查询**: DNS 服务器之间的查询
//! - **缓存机制**: 提高查询效率
//!
//! ## 🔬 实现原理
//!
//! ### DNS 记录类型
//!
//! - **A 记录**: IPv4 地址记录
//! - **AAAA 记录**: IPv6 地址记录
//! - **MX 记录**: 邮件交换记录
//! - **TXT 记录**: 文本记录
//! - **SRV 记录**: 服务记录
//! - **PTR 记录**: 指针记录（逆向解析）
//!
//! ### DNS 解析器类型
//!
//! - **系统解析器**: 使用系统默认 DNS 服务器
//! - **DoH 解析器**: 使用 DNS over HTTPS
//! - **DoT 解析器**: 使用 DNS over TLS
//! - **自定义解析器**: 使用指定的 DNS 服务器
//!
//! ## 🚀 使用场景
//!
//! - **域名解析**: 将域名转换为 IP 地址
//! - **邮件服务**: 查找邮件服务器
//! - **服务发现**: 发现网络服务
//! - **负载均衡**: 基于 DNS 的负载均衡
//!
//! ## ⚠️ 注意事项
//!
//! - **缓存策略**: 合理设置 DNS 缓存
//! - **超时处理**: 处理 DNS 查询超时
//! - **错误处理**: 处理 DNS 查询错误
//! - **安全考虑**: 注意 DNS 劫持和污染
//!
//! ## 🔧 运行方式
//!
//! ```bash
//! # 运行 DNS 查询示例
//! cargo run --example dns_lookup
//! ```
use c10_networks::protocol::dns::{DnsResolver, presets};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    println!("🚀 启动 DNS 查询示例...");

    // 1) 使用系统解析器进行 A/AAAA 记录查询
    println!("\n📡 使用系统解析器查询 A/AAAA 记录:");
    let sys = DnsResolver::from_system().await?;
    let ips = sys.lookup_ips("example.com").await?;
    println!("   域名: example.com");
    println!("   IP 地址: {:?}", ips);
    println!("   说明: A 记录返回 IPv4 地址，AAAA 记录返回 IPv6 地址");

    // 2) 使用 Cloudflare DoH 解析器进行 TXT 记录查询
    println!("\n🔒 使用 Cloudflare DoH 解析器查询 TXT 记录:");
    let (cfg, opts) = presets::cloudflare_doh();
    let doh = DnsResolver::from_config(cfg, opts).await?;
    let txt = doh.lookup_txt("example.com").await?;
    println!("   域名: example.com");
    println!("   TXT 记录: {:?}", txt);
    println!("   说明: TXT 记录通常用于域名验证、SPF 记录等");

    // 3) MX 记录查询（邮件交换记录）
    println!("\n📧 查询 MX 记录（邮件交换记录）:");
    let mx = doh.lookup_mx("gmail.com").await.unwrap_or_default();
    println!("   域名: gmail.com");
    println!("   MX 记录: {:?}", mx);
    println!("   说明: MX 记录指定了处理该域名邮件的邮件服务器");

    // 4) SRV 记录查询（服务记录）
    println!("\n🔍 查询 SRV 记录（服务记录）:");
    let srv = doh
        .lookup_srv("_xmpp-server._tcp.google.com")
        .await
        .unwrap_or_default();
    println!("   服务: _xmpp-server._tcp.google.com");
    println!("   SRV 记录数量: {}", srv.len());
    println!("   说明: SRV 记录用于指定提供特定服务的服务器");

    // 5) 逆向解析（PTR 记录）
    println!("\n🔄 逆向解析（PTR 记录）:");
    if let Some(ip) = ips.first() {
        let names = sys.reverse_lookup(*ip).await.unwrap_or_default();
        println!("   IP 地址: {:?}", ip);
        println!("   域名: {:?}", names);
        println!("   说明: PTR 记录用于将 IP 地址反向解析为域名");
    } else {
        println!("   无法进行逆向解析：没有可用的 IP 地址");
    }

    println!("\n✅ DNS 查询示例完成！");
    Ok(())
}
