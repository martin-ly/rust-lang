//! DNS 查询示例
//! DNS example
//! DNS 查询Example of
//! ## 📖 理论基础
//! ## 📖 theory foundation
//! DNS (域名系统) 是互联网的目录服务，将域名映射到 IP 地址：
//! DNS (domain system ) ，will domain to IP address ：
//! - **分层结构**: 树状域名空间
//! - **layering structure **: tree domain space
//! - **递归查询**: 客户端向 DNS 服务器查询
//! - **recursive **: DNS
//! - ****: DNS
//! - **迭代查询**: DNS 服务器之间的查询
//! - ****: DNS 's
//! - **缓存机制**: 提高查询效率
//! - **cache mechanism **: high efficiency
//! - **mechanism **: efficiency
//! - **缓存mechanism**: 提高查询efficiency
//! ## 🔬 实现原理
//! ## 🔬
//! ## 🔬 Implementation of原理
//! ### DNS 记录类型
//! ### DNS type
//! ### DNS 记录type
//! - **A 记录**: IPv4 地址记录
//! - **A **: IPv4
//! - **AAAA 记录**: IPv6 地址记录
//! - **AAAA **: IPv6
//! - **MX 记录**: 邮件交换记录
//! - **MX **: exchange
//! - **TXT 记录**: 文本记录
//! - **TXT **: this
//! - **SRV 记录**: 服务记录
//! - **SRV **:
//! - **PTR 记录**: 指针记录（逆向解析）
//! - **PTR **: pointer （）
//! ### DNS 解析器类型
//! ### DNS type
//! - **系统解析器**: 使用系统默认 DNS 服务器
//! - **system **: system DNS
//! - **自定义解析器**: 使用指定的 DNS 服务器
//! - **definition **: DNS
//! ## 🚀 使用场景
//! ## 🚀 scenario
//! - **域名解析**: 将域名转换为 IP 地址
//! - **domain **: will domain conversion as IP address
//! - **邮件服务**: 查找邮件服务器
//! - ****:
//! - **服务发现**: 发现网络服务
//! - **service discovery **: network
//! - **负载均衡**: 基于 DNS 的负载均衡
//! - ****: DNS
//! ## ⚠️ 注意事项
//! ## ⚠️
//! - **缓存策略**: 合理设置 DNS 缓存
//! - **cache strategy **: DNS cache
//! - **strategy **: DNS
//! - **缓存strategy**: 合理Set DNS 缓存
//! - **超时处理**: 处理 DNS 查询超时
//! - **timeout **: DNS timeout
//! - ****: DNS
//! - **超时Handle**: Handle DNS 查询超时
//! - **错误处理**: 处理 DNS 查询错误
//! - **error handling **: DNS
//! - **error handling**: Handle DNS 查询错误
//! - **安全考虑**: 注意 DNS 劫持和污染
//! - ****: DNS and
//! ## 🔧 运行方式
//! ## 🔧 Run way
//! ```bash
//! # 运行 DNS 查询示例
//! # Run DNS example
//! # Run DNS 查询Example of
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
    let (cfg, opts) = presets::cloudflare();
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
