use c10_networks::protocol::dns::DnsResolver;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let r = DnsResolver::from_system().await?;

    let domain = std::env::args().nth(1).unwrap_or_else(|| "example.com".to_string());

    let mx = r.lookup_mx(&domain).await?;
    println!("MX => {:?}", mx);

    // 常见 SRV 示例：XMPP、SIP、LDAP 等（需按需替换）
    if let Ok(srv) = r.lookup_srv(&format!("_xmpp-server._tcp.{}", domain)).await {
        println!("SRV(_xmpp-server) => {:?}", srv);
    }

    let txt = r.lookup_txt(&domain).await?;
    println!("TXT => {:?}", txt);

    Ok(())
}


