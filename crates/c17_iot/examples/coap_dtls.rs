// 说明：DTLS 需要额外库支持。此处提供占位与接口示例，便于后续接入 rust-dtls/openssl-deriv 等实现。
// 当前仅构造 CoAP 报文并提示 DTLS 通道未实现。
use coap_lite::{CoapRequest, RequestType};

fn main() -> anyhow::Result<()> {
    let mut req: CoapRequest<std::net::SocketAddr> = CoapRequest::new();
    req.set_method(RequestType::Get);
    req.set_path("/secure");
    let bytes = req.message.to_bytes()?;
    println!("coap over dtls placeholder, frame_len={}", bytes.len());
    println!("TODO: integrate DTLS transport (rustls/openssl/mbedtls binding)");
    Ok(())
}
