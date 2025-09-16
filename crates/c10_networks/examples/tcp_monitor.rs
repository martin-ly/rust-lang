#[cfg(feature = "sniff")]
mod run {
    use c10_networks::sniff::monitor_tcp_once;
    pub fn main() {
        let args: Vec<String> = std::env::args().collect();
        let iface = args.get(1).map(|s| s.as_str());
        let sec: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(5);
        match monitor_tcp_once(iface, sec) {
            Ok(rep) => {
                println!("duration: {:?}", rep.duration);
                println!(
                    "total packets: {} bytes: {}",
                    rep.total.packets, rep.total.bytes
                );
                for (k, v) in rep.by_flow.iter().take(50) {
                    println!("{} -> packets: {} bytes: {}", k, v.packets, v.bytes);
                }
            }
            Err(e) => eprintln!("error: {e}"),
        }
    }
}

#[cfg(not(feature = "sniff"))]
fn main() {
    eprintln!(
        "This example requires feature 'sniff'.\nTry: cargo run -p c10_networks --features sniff --example tcp_monitor -- \"Ethernet\" 5"
    );
}
