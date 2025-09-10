use std::env;

#[tokio::test]
async fn dns_lookup_system_smoke() {
    if env::var("C10_SKIP_NETWORK_TESTS").ok().as_deref() == Some("1") {
        eprintln!("skipped: C10_SKIP_NETWORK_TESTS=1");
        return;
    }

    let r = c10_networks::protocol::dns::DnsResolver::from_system()
        .await
        .expect("system resolver init");
    let ips = r.lookup_ips("example.com").await.expect("resolve example.com");
    assert!(!ips.is_empty());
}

use c10_networks::protocol::dns::{DnsResolver, presets};

#[tokio::test]
async fn dns_system_lookup_ips() {
    if std::env::var("C10_DNS_TESTS").ok().as_deref() != Some("1") {
        eprintln!("skip dns tests: set C10_DNS_TESTS=1 to run");
        return;
    }
    let r = DnsResolver::from_system().await.expect("resolver");
    let ips = r.lookup_ips("example.com").await.expect("ips");
    assert!(!ips.is_empty());
}

#[tokio::test]
async fn dns_doh_txt() {
    if std::env::var("C10_DNS_TESTS").ok().as_deref() != Some("1") {
        eprintln!("skip dns tests: set C10_DNS_TESTS=1 to run");
        return;
    }
    let (cfg, opts) = presets::cloudflare_doh();
    let r = DnsResolver::from_config(cfg, opts).await.expect("resolver");
    let _ = r.lookup_txt("example.com").await.expect("txt");
}


