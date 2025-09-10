use c10_networks::sniff::udp_custom_server;
use std::net::SocketAddr;

#[tokio::main]
async fn main() {
    let addr = std::env::args().nth(1).unwrap_or_else(|| "127.0.0.1:9000".to_string());
    let bind: SocketAddr = addr.parse().expect("invalid addr");
    println!("udp_custom_server listening on {}", bind);
    if let Err(e) = udp_custom_server(bind).await {
        eprintln!("server error: {e}");
    }
}


