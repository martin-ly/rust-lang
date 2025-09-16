use c10_networks::protocol::dns::DnsResolver;
use hickory_resolver::config::{
    NameServerConfig, NameServerConfigGroup, Protocol, ResolverConfig, ResolverOpts,
};
use std::net::{IpAddr, Ipv4Addr, SocketAddr};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let domain = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "internal.service.local".to_string());

    let mut group = NameServerConfigGroup::with_capacity(2);
    group.push(NameServerConfig::new(
        SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 0, 0, 53)), 53),
        Protocol::Udp,
    ));
    group.push(NameServerConfig::new(
        SocketAddr::new(IpAddr::V4(Ipv4Addr::new(1, 1, 1, 1)), 53),
        Protocol::Udp,
    ));

    let cfg = ResolverConfig::from_parts(None, vec![], group);
    let mut opts = ResolverOpts::default();
    opts.attempts = 2;
    opts.cache_size = 1024;
    opts.timeout = std::time::Duration::from_millis(2500);

    let r = DnsResolver::from_config(cfg, opts).await?;
    let ips = r.lookup_ips(&domain).await?;
    println!("{} => {:?}", domain, ips);
    Ok(())
}
