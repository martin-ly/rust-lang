# WebAssembly 实现与工程实践

## 概述

本章系统梳理 Rust 生态下 WebAssembly（WASM）的实现原理、工程落地、优化策略与典型案例，强调类型安全、性能优化与跨平台兼容。

## 理论基础

- WASM 字节码结构与类型系统
- 虚拟机执行模型与安全沙箱
- Rust 到 WASM 的编译流程与内存管理
- 跨语言互操作与 ABI 设计

## 工程实现

### 1. Rust 到 WASM 的编译

```rust
// Cargo.toml
[lib]
crate-type = ["cdylib"]

[dependencies]
wasm-bindgen = "0.2"
```

```rust
// src/lib.rs
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

### 2. JavaScript 互操作

```js
import init, { add } from './your_wasm_pkg.js';
await init();
console.log(add(2, 3)); // 输出 5
```

### 3. 内存管理与性能优化

- 使用 `wasm-bindgen` 管理内存分配与回收
- 利用 `wee_alloc` 等轻量级分配器优化内存占用
- 避免频繁 JS <-> WASM 数据拷贝

## 典型案例

- Web 前端高性能计算模块（如图像处理、音频解码）
- 区块链智能合约运行时（如 Substrate WASM Runtime）
- 跨平台插件系统（如 Figma 插件）

## 批判性分析

- WASM 性能瓶颈主要在于 JS/WASM 边界的数据传递与内存管理
- Rust 的所有权模型有助于提升 WASM 代码安全性，但与 JS GC 机制存在语义差异
- 跨平台兼容性需关注浏览器/Node/独立运行时的差异

## FAQ

- Rust 如何导出复杂类型到 WASM？
  - 需借助 `wasm-bindgen` 提供的类型映射与序列化机制。
- WASM 支持多线程吗？
  - 目前主流浏览器支持 WebAssembly Threads，但需配置 CSP 和 Emscripten。
- 如何调试 WASM？
  - 可用 `wasm-pack` 生成 source map，配合浏览器 DevTools 调试。

## 交叉引用

- [WASM 字节码理论](./02_webassembly_theory.md)
- [虚拟机与安全模型](./01_webassembly_theory.md)
- [Rust 跨平台开发](../21_application_domains/)

## 总结

Rust 生态下的 WebAssembly 实现兼顾了类型安全、性能与跨平台能力。通过标准工具链和最佳实践，开发者可高效构建高性能、可移植的 WASM 应用。
