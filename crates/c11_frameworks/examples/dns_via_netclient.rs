use c10_networks::NetClient;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 可通过环境变量切换解析后端：
    // C10_DNS_BACKEND=cloudflare_doh|cloudflare_dot|google_doh|google_dot|quad9_doh|quad9_dot
    let domain = std::env::args().nth(1).unwrap_or_else(|| "example.com".to_string());
    let api = NetClient::new();
    let ips = api.dns_lookup_ips(&domain).await?;
    println!("{} => {:?}", domain, ips);
    Ok(())
}


