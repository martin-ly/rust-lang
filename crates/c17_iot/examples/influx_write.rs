#[cfg(feature = "influx")]
use influxdb2::Client;
#[cfg(feature = "influx")]
use influxdb2::models::DataPoint;

#[cfg(feature = "influx")]
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 需要 InfluxDB v2：提供 org、bucket 和 token
    let url = std::env::var("INFLUX_URL").unwrap_or_else(|_| "http://127.0.0.1:8086".into());
    let org = std::env::var("INFLUX_ORG").unwrap_or_else(|_| "my-org".into());
    let bucket = std::env::var("INFLUX_BUCKET").unwrap_or_else(|_| "iot".into());
    let token = std::env::var("INFLUX_TOKEN").unwrap_or_else(|_| "my-token".into());

    let client = Client::new(url, token);
    let point = DataPoint::builder("iot_temp")
        .tag("device", "d1")
        .field("value", 21.7)
        .build()?;

    client.write(&org, &bucket, vec![point]).await?;
    println!("influx write ok");
    Ok(())
}

#[cfg(not(feature = "influx"))]
fn main() {
    eprintln!(
        "This example requires the 'influx' feature. Run with: cargo run -p c17_iot --example influx_write --features influx"
    );
}
