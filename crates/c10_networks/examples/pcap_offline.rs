// 需要启用 `--features offline`

#[cfg(feature = "offline")]
mod run {
    use c10_networks::sniff::{parse_pcap_arp, parse_pcap_tcp_stats, parse_pcap_udp_stats};

    pub fn main() {
        let path = std::env::args()
            .nth(1)
            .unwrap_or_else(|| "capture.pcap".to_string());
        match run(&path) {
            Ok(()) => {}
            Err(e) => eprintln!("error: {}", e),
        }
    }

    fn run(path: &str) -> Result<(), Box<dyn std::error::Error>> {
        let arp = parse_pcap_arp(path, Some(50))?;
        let tcp = parse_pcap_tcp_stats(path)?;
        let udp = parse_pcap_udp_stats(path)?;
        println!("pcap: {}", path);
        println!("arp_records={}", arp.len());
        println!("tcp_packets={} tcp_bytes={}", tcp.packets, tcp.bytes);
        println!("udp_packets={} udp_bytes={}", udp.packets, udp.bytes);
        Ok(())
    }
}

#[cfg(not(feature = "offline"))]
fn main() {
    eprintln!(
        "This example requires feature 'offline'.\nTry: cargo run -p c10_networks --features offline --example pcap_offline -- capture.pcap"
    );
}
