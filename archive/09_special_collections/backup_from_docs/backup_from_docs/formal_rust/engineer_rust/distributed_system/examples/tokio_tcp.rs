// 分布式系统：Tokio TCP服务端示例 Distributed System: Tokio TCP Server Example
use tokio::net::TcpListener;

#[tokio::main]
async fn main() {
    let listener = TcpListener::bind("127.0.0.1:8080").await.unwrap();
    println!("Listening on 127.0.0.1:8080");
    loop {
        let (socket, _) = listener.accept().await.unwrap();
        tokio::spawn(async move {
            println!("Accepted connection: {:?}", socket.peer_addr());
        });
    }
} 