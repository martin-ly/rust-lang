use c10_networks::protocol::dns::{DnsResolver, presets};
use std::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let domain = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "example.com".to_string());

    // 优先 DoH（Cloudflare）→ Google DoH → Cloudflare DoT → Google DoT → System
    let ips = if let Ok(v) = try_cloudflare_doh(&domain).await {
        v
    } else if let Ok(v) = try_google_doh(&domain).await {
        v
    } else if let Ok(v) = try_cloudflare_dot(&domain).await {
        v
    } else if let Ok(v) = try_google_dot(&domain).await {
        v
    } else {
        try_system(&domain).await?
    };

    println!("{} => {:?}", domain, ips);
    Ok(())
}

async fn try_cloudflare_doh(domain: &str) -> anyhow::Result<Vec<std::net::IpAddr>> {
    let (cfg, mut opts) = presets::cloudflare_doh();
    opts.timeout = Duration::from_millis(3000);
    let r = DnsResolver::from_config(cfg, opts).await?;
    Ok(r.lookup_ips(domain).await?)
}

async fn try_google_doh(domain: &str) -> anyhow::Result<Vec<std::net::IpAddr>> {
    let (cfg, mut opts) = presets::google_doh();
    opts.timeout = Duration::from_millis(3000);
    let r = DnsResolver::from_config(cfg, opts).await?;
    Ok(r.lookup_ips(domain).await?)
}

async fn try_cloudflare_dot(domain: &str) -> anyhow::Result<Vec<std::net::IpAddr>> {
    let (cfg, mut opts) = presets::cloudflare_dot();
    opts.timeout = Duration::from_millis(3000);
    let r = DnsResolver::from_config(cfg, opts).await?;
    Ok(r.lookup_ips(domain).await?)
}

async fn try_google_dot(domain: &str) -> anyhow::Result<Vec<std::net::IpAddr>> {
    let (cfg, mut opts) = presets::google_dot();
    opts.timeout = Duration::from_millis(3000);
    let r = DnsResolver::from_config(cfg, opts).await?;
    Ok(r.lookup_ips(domain).await?)
}

async fn try_system(domain: &str) -> anyhow::Result<Vec<std::net::IpAddr>> {
    let r = DnsResolver::from_system().await?;
    Ok(r.lookup_ips(domain).await?)
}
