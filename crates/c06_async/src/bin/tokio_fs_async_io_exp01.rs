// 异步文件 I/O 示例（Rust 1.90）
// 说明：使用 tokio::fs 进行读写，并对读操作设置超时

use std::path::PathBuf;
use std::time::Duration;

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    let path = PathBuf::from("./target/tmp/async_demo.txt");

    // 确保目录存在
    if let Some(parent) = path.parent() {
        tokio::fs::create_dir_all(parent).await?;
    }

    // 写入文件（覆盖）
    let content = b"hello async fs\n";
    tokio::fs::write(&path, content).await?;

    // 读文件并设置 1s 超时
    let read_fut = tokio::fs::read(&path);
    let bytes = tokio::time::timeout(Duration::from_secs(1), read_fut).await??;
    println!("read {} bytes: {}", bytes.len(), String::from_utf8_lossy(&bytes));

    Ok(())
}


