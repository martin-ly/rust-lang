# 实践项目 06: 并发下载器
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **分级**: [A]
> **Bloom 层级**: L3 (应用)
> **难度**: ⭐⭐ 进阶级
> **所需知识**: c05-c06 (线程、异步)
> **预计时间**: 4-6小时

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [实践项目 06: 并发下载器](.#实践项目-06-并发下载器)
  - [📑 目录](.#-目录)
  - [项目目标](.#项目目标)
  - [功能需求](.#功能需求)
  - [学习要点](.#学习要点)
    - [多线程下载](.#多线程下载)
    - [异步下载](.#异步下载)
  - [参考实现](.#参考实现)
  - [相关概念](.#相关概念)
  - [权威来源索引](.#权威来源索引)

## 项目目标
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

创建一个支持并发下载的文件下载器。

---

## 功能需求
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- [ ] 多线程下载
- [ ] 断点续传
- [ ] 下载进度显示
- [ ] 限速功能

---

## 学习要点
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 多线程下载

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

```rust,ignore
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
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
use tokio;

async fn download_async(url: &str) -> Result<Vec<u8>, reqwest::Error> {
    let response = reqwest::get(url).await?;
    let bytes = response.bytes().await?;
    Ok(bytes.to_vec())
}
```

---

## 参考实现
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

完整参考实现位于: `examples/concurrent-downloader/`

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](README.md)

---

## 相关概念
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [03_practice 目录](README.md)
- [docs 索引](../README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Concurrency](https://en.wikipedia.org/wiki/Concurrency)**
> **来源: [TRPL Ch. 16 - Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)**
> **来源: [crossbeam Documentation](https://docs.rs/crossbeam/latest/crossbeam/)**
> **来源: [ACM - Concurrent Programming](https://dl.acm.org/)**

---
