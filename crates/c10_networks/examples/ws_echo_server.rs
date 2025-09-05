use futures_util::{SinkExt, StreamExt};
use tokio::net::TcpListener;
use tokio_tungstenite::tungstenite::Message;
use tokio_tungstenite::accept_async;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let listener = TcpListener::bind("127.0.0.1:9001").await?;
    println!("WebSocket server listening on ws://127.0.0.1:9001");

    loop {
        let (stream, _addr) = listener.accept().await?;
        tokio::spawn(async move {
            if let Ok(mut ws) = accept_async(stream).await {
                while let Some(msg) = ws.next().await {
                    match msg {
                        Ok(Message::Text(t)) => { let _ = ws.send(Message::Text(t)).await; }
                        Ok(Message::Binary(b)) => { let _ = ws.send(Message::Binary(b)).await; }
                        Ok(Message::Close(_)) => break,
                        _ => {}
                    }
                }
            }
        });
    }
}


