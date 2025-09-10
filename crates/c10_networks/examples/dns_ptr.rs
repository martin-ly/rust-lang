use c10_networks::protocol::dns::DnsResolver;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let r = DnsResolver::from_system().await?;
    let ip: std::net::IpAddr = "1.1.1.1".parse()?;
    let names = r.reverse_lookup(ip).await?;
    println!("PTR => {:?}", names);
    Ok(())
}


