use futures_util::{SinkExt, StreamExt};
use tokio_tungstenite::connect_async;
use tokio_tungstenite::tungstenite::Message;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let url = "ws://127.0.0.1:9001";
    let (mut ws, _resp) = connect_async(url).await?;
    ws.send(Message::Text("hello ws".into())).await?;
    if let Some(msg) = ws.next().await {
        println!("recv: {:?}", msg);
    }
    Ok(())
}
