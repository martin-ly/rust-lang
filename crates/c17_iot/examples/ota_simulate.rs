use sha2::{Digest, Sha256};

// 模拟 OTA：校验镜像哈希，写入“分区”，失败则回滚
fn main() -> anyhow::Result<()> {
    let new_firmware = b"firmware-v2.0-image";
    let expected = hex::encode(Sha256::digest(new_firmware));
    let recv = new_firmware; // 模拟下载完成

    let actual = hex::encode(Sha256::digest(recv));
    if actual != expected {
        println!("hash mismatch, rollback");
        return Ok(());
    }

    // 模拟写入与标记成功
    let mut active = String::from("v1.0");
    println!("before active={}", active);
    active = "v2.0".into();
    println!("after active={}", active);
    Ok(())
}


