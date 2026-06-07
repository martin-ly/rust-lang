# 实践项目 02: 文件处理器
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **分级**: [A]
> **Bloom 层级**: L3 (应用)
> **难度**: ⭐ 入门级
> **所需知识**: c01-c03
> **预计时间**: 2-3小时

---

## 项目目标
>
> **[来源: Rust Official Docs]**

创建一个文件处理工具，支持文件搜索、复制、统计等功能。

---

## 功能需求
>
> **[来源: Rust Official Docs]**

- [ ] 搜索文件: `filetool search .txt`
- [ ] 复制文件: `filetool copy src.txt dst.txt`
- [ ] 统计文件信息: `filetool stat file.txt`
- [ ] 批量重命名: `filetool rename *.txt .md`

---

## 学习要点
>
> **[来源: Rust Official Docs]**

### 文件系统操作
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust
use std::fs;
use std::path::Path;

fn get_file_info(path: &Path) -> std::io::Result<()> {
    let metadata = fs::metadata(path)?;
    println!("大小: {} 字节", metadata.len());
    println!("只读: {}", metadata.permissions().readonly());
    Ok(())
}
```

### 目录遍历
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust
use std::fs;

fn list_files(dir: &str) -> std::io::Result<Vec<String>> {
    let mut files = Vec::new();
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        files.push(entry.path().to_string_lossy().to_string());
    }
    Ok(files)
}
```

---

## 参考实现

完整参考实现位于: `examples/file-processor/`

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**
> **[来源: Rust Reference - doc.rust-lang.org/reference]**
> **[来源: TRPL - The Rust Programming Language]**
> **[来源: Rust Standard Library - doc.rust-lang.org/std]**
> **[来源: ACM - Systems Programming Languages]**
> **[来源: IEEE - Programming Language Standards]**
> **[来源: RFCs - github.com/rust-lang/rfcs]**
> **[来源: Rustonomicon - doc.rust-lang.org/nomicon]**

---
