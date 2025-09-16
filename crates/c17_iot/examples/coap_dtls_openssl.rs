// CoAP over DTLS（OpenSSL）占位示例：当前仅构建 DTLS Connector 以验证依赖，未实现跨平台的 DTLS 传输。
// 生产环境请使用成熟 DTLS 绑定或库，并开启证书/PSK 校验。
#[cfg(feature = "openssl-examples")]
use openssl::ssl::{SslContextBuilder, SslMethod};

#[cfg(feature = "openssl-examples")]
fn main() -> anyhow::Result<()> {
    let _ctx = SslContextBuilder::new(SslMethod::dtls())?;
    println!("coap-dtls-openssl: 占位示例（未实现跨平台数据通道）");
    Ok(())
}

#[cfg(not(feature = "openssl-examples"))]
fn main() {
    println!("coap-dtls-openssl: 未启用特性 `openssl-examples`，跳过 OpenSSL 依赖");
}
