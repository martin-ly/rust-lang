# 概览：WebAssembly（c16_webassembly）

本模块聚焦 Rust 到 Wasm 的构建、ABI 与运行时集成，并整理典型场景的实践要点与版本对齐。

---

## 目录导航

- Rust WebAssembly 视图
  - `rust_webassembly/view01.md` … `view13.md`

- 顶层与示例
  - 顶层说明：`README.md`
  - 章节引导：`12_webassembly.md`
  - 源码：`src/`

---

## 快速开始

1) 阅读 `rust_webassembly/view01.md`
2) 构建 `src/` 示例并在浏览器/wasmtime 运行
3) 关注 ABI、内存、宿主交互的边界

---

## 待完善

- 增补 `wasm32-wasi` 与 `wasm64` 的兼容性清单
- 与 `c11_frameworks` 前端/后端集成链路互链
