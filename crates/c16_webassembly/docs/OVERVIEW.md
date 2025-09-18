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

### 目标平台兼容性清单（wasm32-wasi 与 wasm64）（补全）

- 目标三元组
  - wasm32-wasi：32 位指针，WASI（Preview1/Preview2）能力由运行时决定
  - wasm64-unknown-unknown / wasm64-wasi：64 位指针（memory64），更大地址空间

- 运行时与支持要点
  - wasmtime/wasmer：优先支持 WASI、组件模型演进；memory64 支持需使用较新版本
  - Node.js/浏览器：主要面向 wasm32；wasm64 与组件模型仍在逐步落地

- 语言/编译器注意事项
  - `wasm32` 与 `wasm64` 的 `usize`/指针宽度不同，影响 FFI 与内存布局
  - memory64 需要工具链与运行时共同支持；第三方库的 `usize` 假设需审查

- 构建与测试建议
  - 交叉构建：`cargo build --target wasm32-wasi`（或 wasm64 目标）
  - 单元测试：优先在宿主侧运行逻辑测试，WASI 集成测试用 wasmtime 驱动
  - ABI 边界：以 `wit`/`wit-bindgen` 描述接口，降低平台差异

- 兼容性检查清单
  - 不依赖未实现的 `std::fs`/`std::net` 能力；以 WASI 能力模型声明最小权限
  - 明确线性内存增长策略；避免隐式假设“指针==u32”
  - 验证 `#[repr(C)]` 结构在 32/64 位上的对齐与大小
  - 第三方依赖是否限定 wasm32；必要时选择 `no_std` 方案

- 集成链路
  - 与 `c11_frameworks`：前端（wasm-bindgen/worker）与后端（WASI 服务）接口一致化
  - 与 `c06_async`：结合异步执行器与宿主回调的协作模式
