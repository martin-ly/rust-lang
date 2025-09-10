use c10_networks::unified_api::NetClient;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 可通过 C10_DNS_BACKEND=cloudflare_doh 切换解析器
    let api = NetClient::new();
    let ips = api.dns_lookup_ips("example.com").await?;
    println!("ips: {:?}", ips);
    if let Some(ip) = ips.first() {
        let names = api.dns_reverse(*ip).await.unwrap_or_default();
        println!("reverse {:?} => {:?}", ip, names);
    }
    Ok(())
}


