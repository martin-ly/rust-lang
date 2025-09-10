use c10_networks::protocol::dns::{presets, DnsResolver};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 1) 使用系统解析器
    let sys = DnsResolver::from_system().await?;
    let ips = sys.lookup_ips("example.com").await?;
    println!("system A/AAAA: {:?}", ips);

    // 2) 使用 Cloudflare DoH 解析器
    let (cfg, opts) = presets::cloudflare_doh();
    let doh = DnsResolver::from_config(cfg, opts).await?;
    let txt = doh.lookup_txt("example.com").await?;
    println!("doh TXT: {:?}", txt);

    // 4) MX / SRV 查询（存在性依域名而定）
    let mx = doh.lookup_mx("gmail.com").await.unwrap_or_default();
    println!("MX gmail.com => {:?}", mx);
    let srv = doh.lookup_srv("_xmpp-server._tcp.google.com").await.unwrap_or_default();
    println!("SRV google.com => count={}", srv.len());

    // 3) 逆向解析
    if let Some(ip) = ips.first() {
        let names = sys.reverse_lookup(*ip).await.unwrap_or_default();
        println!("reverse {:?} => {:?}", ip, names);
    }

    Ok(())
}


