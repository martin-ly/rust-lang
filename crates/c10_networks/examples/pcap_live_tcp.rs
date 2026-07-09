// 需要启用 --features pcap-live

#[cfg(feature = "pcap-live")]
#[tokio::main]
async fn main() {
    run::main().await;
}

#[cfg(feature = "pcap-live")]
mod run {
    use c10_networks::sniff::tcp_stats_stream_bpf;
    use std::time::Duration;

    pub async fn main() {
        let dev = std::env::args()
            .nth(1)
            .unwrap_or_else(|| "Ethernet".to_string());
        let bpf = std::env::args().nth(2).unwrap_or_else(|| "tcp".to_string());
        let mut rx = tcp_stats_stream_bpf(&dev, &bpf, Duration::from_secs(2), 128)
            .await
            .expect("open live");
        println!("device={} bpf=\"{}\"", dev, bpf);
        while let Some((t, stats)) = rx.recv().await {
            let _ = t; // timestamp
            println!("tcp packets={} bytes={}", stats.packets, stats.bytes);
        }
    }
}

#[cfg(not(feature = "pcap-live"))]
fn main() {
    eprintln!(
        "This example requires feature 'pcap-live'.\nTry: cargo run -p c10_networks --features \
         pcap-live --example pcap_live_tcp -- \"Ethernet\" \"tcp port 80\""
    );
}
