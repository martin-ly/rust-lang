# 实践项目 02: 文件处理器

> **难度**: ⭐ 入门级
> **所需知识**: c01-c03
> **预计时间**: 2-3小时

---

## 项目目标

创建一个文件处理工具，支持文件搜索、复制、统计等功能。

---

## 功能需求

- [ ] 搜索文件: `filetool search .txt`
- [ ] 复制文件: `filetool copy src.txt dst.txt`
- [ ] 统计文件信息: `filetool stat file.txt`
- [ ] 批量重命名: `filetool rename *.txt .md`

---

## 学习要点

### 文件系统操作

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
