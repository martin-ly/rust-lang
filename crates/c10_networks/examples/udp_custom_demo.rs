#[cfg(feature = "sniff")]
mod run {
    use c10_networks::sniff::{UdpCustomMessage, udp_custom_roundtrip};

    #[tokio::main]
    pub async fn main() {
        let args: Vec<String> = std::env::args().collect();
        let addr = args
            .get(1)
            .cloned()
            .unwrap_or_else(|| "127.0.0.1:9000".to_string());
        let msg = UdpCustomMessage {
            version: 1,
            msg_type: 1,
            payload: b"hello".to_vec(),
        };
        match udp_custom_roundtrip(&addr, &msg).await {
            Ok(resp) => println!(
                "resp: v={} t={} payload={:?}",
                resp.version,
                resp.msg_type,
                String::from_utf8_lossy(&resp.payload)
            ),
            Err(e) => eprintln!("error: {e}"),
        }
    }
}

#[cfg(not(feature = "sniff"))]
fn main() {
    eprintln!(
        "This example requires feature 'sniff'.\nTry: cargo run -p c10_networks --features sniff --example udp_custom_demo -- 127.0.0.1:9000"
    );
}

#[cfg(feature = "sniff")]
pub use run::main;
