# C12 WebAssembly - 一页纸总结

> **用途**: 快速回顾核心概念、常见坑、学习路径
> **完整文档**: [tier_01_foundations/02_主索引导航](./tier_01_foundations/02_主索引导航.md)

---

## 核心概念（4 条）

| 概念 | 说明 |
| :--- | :--- || **WASM 基础** | 二进制格式、栈机、线性内存；跨平台 |
| **wasm-bindgen** | Rust↔JS 绑定；`#[wasm_bindgen]`；类型映射 |
| **WASI** | 系统接口；文件、网络；服务端 WASM |
| **构建工具** | `wasm-pack`；`trunk`；target `wasm32-unknown-unknown` |

---

## 常见坑与解决

| 坑 | 解决 |
| :--- | :--- || 包体积过大 | `opt-level = "z"`；`wasm-opt`；避免拉入 std 全量 |
| JS 互操作类型 | 用 `JsValue`、`serde_wasm_bindgen`；注意 ABI |
| 异步 bridge | `wasm_bindgen_futures`；`Promise` 转换 |
| 调试困难 | `console_error_panic_hook`；source map |

---

## WASM 速选

| 场景 | 选型 |
| :--- | :--- || 前端集成 | wasm-bindgen + wasm-pack |
| 服务端/边缘 | WASI；wasmtime、WasmEdge |
| 纯计算模块 | 最小化导出；无 JS 依赖 |
| 游戏/图形 | wgpu；raw WebGL |

---

## 学习路径

1. **入门** (1–2 周): wasm-pack 入门 → 简单函数导出 → 前端调用
2. **进阶** (2–3 周): 复杂类型、异步、性能优化
3. **高级** (持续): WASI、组件模型、生产部署

---

## 速查与练习

- **速查卡**: [wasm_cheatsheet](../../../docs/02_reference/quick_reference/wasm_cheatsheet.md)
- **RBE 练习**: 无 WASM 专题；参考 [wasm-bindgen](https://rustwasm.github.io/wasm-bindgen/)
- **Rustlings**: 无 WASM 专题；参考 C12 模块
