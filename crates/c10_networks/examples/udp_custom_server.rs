#[cfg(any(feature = "sniff", feature = "offline", feature = "pcap_live"))]
use c10_networks::sniff::udp_custom_server;
#[cfg(any(feature = "sniff", feature = "offline", feature = "pcap_live"))]
use std::net::SocketAddr;

#[cfg(not(any(feature = "sniff", feature = "offline", feature = "pcap_live")))]
fn main() {
    eprintln!(
        "This example requires feature 'sniff' (or 'offline'/'pcap_live').\nRun: cargo run -p c10_networks --features sniff --example udp_custom_server -- 127.0.0.1:9000"
    );
}

#[cfg(any(feature = "sniff", feature = "offline", feature = "pcap_live"))]
#[tokio::main]
async fn main() {
    let addr = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "127.0.0.1:9000".to_string());
    let bind: SocketAddr = addr.parse().expect("invalid addr");
    println!("udp_custom_server listening on {}", bind);
    if let Err(e) = udp_custom_server(bind).await {
        eprintln!("server error: {e}");
    }
}
