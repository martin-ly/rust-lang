# I/O 操作

> **核心库**: tokio::fs, async-std::fs, memmap2, walkdir  
> **适用场景**: 文件操作、目录遍历、内存映射、异步I/O

---

## 📋 核心库概览

| 库 | 用途 | 特点 | 推荐度 |
|-----|------|------|--------|
| **tokio::fs** | 异步文件I/O | 高性能 | ⭐⭐⭐⭐⭐ |
| **memmap2** | 内存映射文件 | 高效读取 | ⭐⭐⭐⭐⭐ |
| **walkdir** | 目录遍历 | 易用、可靠 | ⭐⭐⭐⭐⭐ |

---

## 📁 异步文件操作

```rust
use tokio::fs;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn main() -> std::io::Result<()> {
    // 读取文件
    let contents = fs::read_to_string("file.txt").await?;
    println!("{}", contents);
    
    // 写入文件
    fs::write("output.txt", b"Hello, World!").await?;
    
    // 追加文件
    let mut file = fs::OpenOptions::new()
        .append(true)
        .open("log.txt")
        .await?;
    file.write_all(b"Log entry\n").await?;
    
    Ok(())
}
```

---

## 🗺️ 内存映射文件

```rust
use memmap2::Mmap;
use std::fs::File;

fn main() -> std::io::Result<()> {
    let file = File::open("large_file.dat")?;
    let mmap = unsafe { Mmap::map(&file)? };
    
    // 零拷贝访问文件内容
    let data = &mmap[0..100];
    println!("{:?}", data);
    
    Ok(())
}
```

---

## 🚶 目录遍历

```rust
use walkdir::WalkDir;

fn main() {
    for entry in WalkDir::new(".").follow_links(true) {
        let entry = entry.unwrap();
        println!("{}", entry.path().display());
    }
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
