#[cfg(feature = "sniff")]
mod run {
    use c10_networks::sniff::{ArpSniffConfig, ArpSniffer};
    pub fn main() {
        let args: Vec<String> = std::env::args().collect();
        let iface = args.get(1).cloned();
        let cfg = ArpSniffConfig {
            iface_name: iface,
            promiscuous: true,
        };
        match ArpSniffer::sniff_arp_sync(cfg, Some(10)) {
            Ok(records) => {
                for r in records {
                    println!("{:?}", r);
                }
            }
            Err(e) => eprintln!("error: {e}"),
        }
    }
}

#[cfg(not(feature = "sniff"))]
fn main() {
    eprintln!(
        "This example requires feature 'sniff'.\nTry: cargo run -p c10_networks --features sniff --example arp_sniff -- \"Ethernet\""
    );
}
