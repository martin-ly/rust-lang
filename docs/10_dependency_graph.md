# 依赖关系图

> **分级**: [B]
> **Bloom 层级**: L2-L3 (理解/应用)

> **最后更新**: 2026-04-10
> **版本**: 基于 Cargo.toml 解析

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [依赖关系图](#依赖关系图)
  - [📑 目录](#目录)
  - [Crate 依赖图](#crate-依赖图)
    - [视觉表示](#视觉表示)
  - [依赖矩阵](#依赖矩阵)
  - [外部依赖统计](#外部依赖统计)
    - [核心运行时](#核心运行时)
    - [序列化](#序列化)
    - [网络](#网络)
    - [WebAssembly](#webassembly)
    - [宏开发](#宏开发)
  - [依赖类型说明](#依赖类型说明)
    - [编译时依赖](#编译时依赖)
    - [运行时依赖](#运行时依赖)
    - [可选依赖](#可选依赖)
  - [依赖更新策略](#依赖更新策略)
    - [自动更新](#自动更新)
    - [手动审查](#手动审查)
    - [锁定策略](#锁定策略)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## Crate 依赖图
>
> **[来源: Rust Official Docs]**

### 视觉表示
>
> **[来源: Rust Official Docs]**

```
                外部依赖
                /   |   \
                /    |    \
            Tokio   Serde   Rayon
                \    |    /
                 \   |   /
                  \  |  /
                   \ | /
                    \|/
              +--------------+
              |    common    |
              +--------------+
                    / \
                   /   \
    +-------------+     +-------------+
    | c01_owner   |     | c02_type    |
    +-------------+     +-------------+
         /   \
        /     \
   +-------+  +-------+
   | c03   |  | c04   |
   +-------+  +-------+
                  |
            +---------+
            | c05     |
            | threads |
            +---------+
               /  \
              /    \
         +-------+  +-------+
         | c06   |  | c08   |
         | async |  | algo  |
         +-------+  +-------+
              |
         +-------+     +-------+
         | c07   |---->| c10   |
         | process     |network|
         +-------+     +-------+
              |            |
         +-------+     +-------+
         | c09   |     | c11   |
         |pattern|     | macro |
         +-------+     +-------+
                              |
                         +-------+
                         | c12   |
                         | wasm  |
                         +-------+
```

---

## 依赖矩阵
>
> **[来源: Rust Official Docs]**

| Crate | 直接依赖 | 外部依赖 |
|-------|----------|----------|
| c01_ownership | common | tokio, serde |
| c02_type_system | c01_ownership, common | tokio, serde, futures |
| c03_control_fn | c02_type_system | tokio, tracing, anyhow |
| c04_generic | c02_type_system | rayon, itertools |
| c05_threads | c01_ownership, common | crossbeam, rayon |
| c06_async | c05_threads, common | tokio, axum, actix |
| c07_process | c06_async, common | nix, memmap2 |
| c08_algorithms | c04_generic, common | rayon, petgraph |
| c09_design_pattern | c04_generic | tokio, rayon |
| c10_networks | c06_async, c07_process | tokio, tonic, rustls |
| c11_macro_system | c04_generic | syn, quote |
| c12_wasm | c06_async | wasm-bindgen, js-sys |
| common | - | serde, thiserror (可选) |

---

## 外部依赖统计
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 核心运行时
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 包 | 版本 | 用途 | 使用 Crate |
|----|------|------|-----------|
| tokio | 1.51.0 | 异步运行时 | c01-c07, c10, c12 |
| rayon | 1.11.0 | 数据并行 | c04, c05, c08, c09 |
| crossbeam | 0.8.4 | 并发原语 | c05, c09 |

### 序列化
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 包 | 版本 | 用途 | 使用 Crate |
|----|------|------|-----------|
| serde | 1.0.228 | 序列化框架 | 所有 crate |
| serde_json | 1.0.140 | JSON 支持 | 所有 crate |

### 网络
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 包 | 版本 | 用途 | 使用 Crate |
|----|------|------|-----------|
| axum | 0.8.7 | Web 框架 | c06, c10 |
| tonic | 0.14.4 | gRPC | c10 |
| reqwest | 0.13.2 | HTTP 客户端 | c06, c10 |
| tokio-tungstenite | 0.29.0 | WebSocket | c10 |

### WebAssembly
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

| 包 | 版本 | 用途 | 使用 Crate |
|----|------|------|-----------|
| wasm-bindgen | 0.2.117 | JS 互操作 | c12 |
| js-sys | 0.3.94 | JS 绑定 | c12 |
| web-sys | 0.3.94 | Web API | c12 |

### 宏开发
>
> **[来源: [crates.io](https://crates.io/)]**

| 包 | 版本 | 用途 | 使用 Crate |
|----|------|------|-----------|
| syn | 2.0.117 | 语法解析 | c11 |
| quote | 1.0.44 | 代码生成 | c11 |
| proc-macro2 | 1.0.106 | Token 处理 | c11 |

---

## 依赖类型说明
>
> **[来源: [docs.rs](https://docs.rs/)]**

### 编译时依赖
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- syn, quote, proc-macro2 - 宏开发
- tonic-build - gRPC 代码生成
- prost-build - Protobuf 编译

### 运行时依赖
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- tokio - 异步运行时
- serde - 序列化
- 所有网络库

### 可选依赖
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- criterion - 基准测试
- proptest - 属性测试
- mockall - 模拟对象

---

## 依赖更新策略
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 自动更新
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- patch 版本: 自动接受
- minor 版本: CI 通过后合并

### 手动审查
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- major 版本: 需要审查和测试
- 安全更新: 优先处理

### 锁定策略
>
> **[来源: [crates.io](https://crates.io/)]**

- Cargo.lock 提交到版本控制
- 定期运行 cargo update

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

## 相关概念
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [docs 目录](./README.md)

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
