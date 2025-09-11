use coap_lite::{CoapOption, CoapRequest, MessageClass, Packet};
use std::net::UdpSocket;

// 极简 CoAP GET + Observe 报文构造并发送到本地 5683 端口。
// 需要本地有 CoAP 服务器（如 libcoap 示例）以便看到响应。
fn main() -> anyhow::Result<()> {
    let socket = UdpSocket::bind("0.0.0.0:0")?;
    socket.connect("127.0.0.1:5683")?;

    let mut req: CoapRequest<std::net::SocketAddr> = CoapRequest::new();
    req.message.header.message_id = 0x1234;
    req.set_method(coap_lite::RequestType::Get);
    req.set_path("/sensors/temp");

    // Observe=0 注册观察
    {
        let mut pkt: Packet = req.message.clone();
        pkt.set_token(vec![1, 2, 3, 4]);
        pkt.add_option(CoapOption::Observe, vec![0]);
        req.message = pkt;
    }

    let bytes = req.message.to_bytes()?;
    socket.send(&bytes)?;

    let mut buf = [0u8; 1500];
    if let Ok(n) = socket.recv(&mut buf) {
        let resp = Packet::from_bytes(&buf[..n])?;
        match resp.header.code {
            MessageClass::Response(code) => {
                println!("coap resp code={:?} payload={:?}", code, String::from_utf8_lossy(&resp.payload));
            }
            _ => println!("coap unknown message"),
        }
    } else {
        println!("no coap response");
    }

    Ok(())
}


