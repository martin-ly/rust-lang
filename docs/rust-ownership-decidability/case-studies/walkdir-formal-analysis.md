# Walkdir 目录遍历形式化分析

> **主题**: 安全递归目录遍历
>
> **形式化框架**: 遍历顺序 + 循环检测
>
> **参考**: walkdir Documentation

---

## 目录

- [Walkdir 目录遍历形式化分析](#walkdir-目录遍历形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 遍历顺序](#2-遍历顺序)
    - [定理 2.1 (内容优先 vs 目录优先)](#定理-21-内容优先-vs-目录优先)
  - [3. 符号链接处理](#3-符号链接处理)
    - [定理 3.1 (链接控制)](#定理-31-链接控制)
  - [4. 循环检测](#4-循环检测)
    - [定理 4.1 (自动循环检测)](#定理-41-自动循环检测)
  - [5. 反例](#5-反例)
    - [反例 5.1 (TOCTOU)](#反例-51-toctou)
    - [反例 5.2 (路径长度)](#反例-52-路径长度)

---

## 1. 引言

walkdir提供:

- 递归目录遍历
- 可配置排序
- 符号链接控制
- 循环检测

---

## 2. 遍历顺序

### 定理 2.1 (内容优先 vs 目录优先)

> 可选择遍历顺序。

```rust
WalkDir::new(".")
    .contents_first(true)   // 文件先于目录
    .into_iter()

WalkDir::new(".")
    .contents_first(false)  // 目录先于文件(默认)
```

∎

---

## 3. 符号链接处理

### 定理 3.1 (链接控制)

> 默认不跟随符号链接。

```rust
WalkDir::new(".")
    .follow_links(true)     // 跟随符号链接
    .max_open(10)           // 限制同时打开文件数
```

∎

---

## 4. 循环检测

### 定理 4.1 (自动循环检测)

> 检测并跳过循环链接。

```rust
for entry in WalkDir::new(".").follow_links(true) {
    match entry {
        Ok(e) => println!("{}", e.path().display()),
        Err(e) if e.loop_from().is_some() => {
            // 检测到循环，跳过
        }
        Err(e) => return Err(e),
    }
}
```

∎

---

## 5. 反例

### 反例 5.1 (TOCTOU)

```rust
for entry in WalkDir::new(".") {
    let entry = entry?;
    let path = entry.path();
    // entry.metadata()是遍历时的快照
    // 实际文件可能已变更
    let size = std::fs::metadata(path)?.len();  // 重新获取
}
```

### 反例 5.2 (路径长度)

```rust
// Windows长路径可能失败
WalkDir::new("\\\\?\\C:\\very\\long\\path...")
```

---

*文档版本: 1.0.0*
*定理数量: 4个*
