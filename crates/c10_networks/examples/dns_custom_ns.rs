use c10_networks::protocol::dns::DnsResolver;
use hickory_resolver::config::{ConnectionConfig, NameServerConfig, ResolverConfig, ResolverOpts};
use std::net::{IpAddr, Ipv4Addr};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let domain = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "internal.service.local".to_string());

    let mut name_servers = Vec::with_capacity(2);
    name_servers.push(NameServerConfig::new(
        IpAddr::V4(Ipv4Addr::new(10, 0, 0, 53)),
        false,
        vec![ConnectionConfig::udp()],
    ));
    name_servers.push(NameServerConfig::new(
        IpAddr::V4(Ipv4Addr::new(1, 1, 1, 1)),
        false,
        vec![ConnectionConfig::udp()],
    ));

    let cfg = ResolverConfig::from_parts(None, vec![], name_servers);
    let mut opts = ResolverOpts::default();
    opts.attempts = 2;
    opts.cache_size = 1024;
    opts.timeout = std::time::Duration::from_millis(2500);

    let r = DnsResolver::from_config(cfg, opts).await?;
    let ips = r.lookup_ips(&domain).await?;
    println!("{} => {:?}", domain, ips);
    Ok(())
}
