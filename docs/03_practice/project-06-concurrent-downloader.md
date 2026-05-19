# 实践项目 06: 并发下载器

> **难度**: ⭐⭐ 进阶级
> **所需知识**: c05-c06 (线程、异步)
> **预计时间**: 4-6小时

---

## 项目目标

创建一个支持并发下载的文件下载器。

---

## 功能需求

- [ ] 多线程下载
- [ ] 断点续传
- [ ] 下载进度显示
- [ ] 限速功能

---

## 学习要点

### 多线程下载

```rust
use std::thread;
use std::sync::{Arc, Mutex};

fn download_concurrent(urls: Vec<String>) {
    let mut handles = vec![];
    let progress = Arc::new(Mutex::new(0));

    for url in urls {
        let prog = Arc::clone(&progress);
        let handle = thread::spawn(move || {
            download(&url);
            *prog.lock().unwrap() += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 异步下载

```rust
use tokio;

async fn download_async(url: &str) -> Result<Vec<u8>, reqwest::Error> {
    let response = reqwest::get(url).await?;
    let bytes = response.bytes().await?;
    Ok(bytes.to_vec())
}
```

---

## 参考实现

完整参考实现位于: `examples/concurrent-downloader/`
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
