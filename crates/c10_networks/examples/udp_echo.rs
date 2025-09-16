use tokio::net::UdpSocket;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let socket = UdpSocket::bind("127.0.0.1:9002").await?;
    println!("UDP echo listening on 127.0.0.1:9002");

    let mut buf = vec![0u8; 1500];
    loop {
        let (n, peer) = socket.recv_from(&mut buf).await?;
        socket.send_to(&buf[..n], &peer).await?;
    }
}
