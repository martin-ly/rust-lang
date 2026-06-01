//! Wasm Performance

#![forbid(unsafe_code)]

//! 本模块涵盖 WASM 二进制体积优化、启动时间优化、JS/WASM 边界开销分析，
//! this module cover WASM volume optimization 、time optimization 、JS/WASM edge overhead analyze ，
//! this module WASM volume optimization 、time optimization 、JS/WASM edge overhead analyze ，
//! and wasm-bindgen and wasm-pack 构建选项to比。

// ============================================================================
// 1. BinarySizeOptimization — WASM 二进制体积优化
// ============================================================================

/// WASM 二进制体积优化策略
/// WASM volume optimization strategy
pub struct BinarySizeOptimization;

impl BinarySizeOptimization {
    /// 优化策略总览
    /// optimization strategy
    pub fn overview() -> &'static str {
        r#"=== WASM 二进制体积优化策略 ===

1. wasm-opt（Binaryen 工具链）
   - 使用 `-O` / `-Os` / `-Oz` 进行死代码消除、指令合并
   - `-Oz` 极致压缩，可能牺牲少量性能
   - 集成到 wasm-pack 构建流程：`wasm-pack build --release`

2. wee_alloc（轻量级分配器）
   - 替换默认的 dlmalloc，减少分配器本身体积 (~10KB -> ~1KB)
   - 适用场景：对体积敏感、分配频率不高的应用
   - 注意：大对象/高频分配场景性能较差

3. 编译配置优化
   - `opt-level = "z"` / `opt-level = "s"`
   - `lto = true` / `lto = "fat"`
   - `codegen-units = 1`
   - `strip = true` 去除调试符号

4. 依赖裁剪
   - 使用 `cargo tree` 分析依赖体积
   - 替换重型 crate 为轻量替代（如 serde -> miniserde）
   - 禁用不必要的 feature
"#
    }

    /// wasm-opt 详解
    pub fn wasm_opt() -> &'static str {
        r#"=== wasm-opt 详解 ===

wasm-opt 是 WebAssembly Binaryen 工具链的优化器：

常用级别：
- `-O0`：无优化
- `-O1` / `-O2` / `-O3`：标准优化级别
- `-Os`：优化体积，保留合理性能
- `-Oz`：极致体积优化

关键优化 Pass：
- dce（Dead Code Elimination）：移除未使用函数
- inlining：控制函数内联阈值
- duplicate-function-elimination：合并相同函数体
- memory-packing：压缩数据段

在 wasm-pack 中使用：
```bash
wasm-pack build --release --target web
# 默认会自动调用 wasm-opt
```

手动调用：
```bash
wasm-opt -Oz -o output.wasm input.wasm
```
"#
    }

    /// wee_alloc 概念
    pub fn wee_alloc_concept() -> &'static str {
        r#"=== wee_alloc 概念 ===

wee_alloc 是一个为 WebAssembly 设计的简单分配器：

特点：
- 代码体积极小（约 1KB WASM）
- 使用首次适应（first-fit）算法
- 不依赖外部 libc

权衡：
- 分配/释放性能不如 dlmalloc
- 长时间运行可能产生碎片
- 不适合高频大对象分配

使用方式：
```toml
[dependencies]
wee_alloc = "0.4"
```

```rust
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;
```

建议：仅在二进制体积为首要约束时使用，否则保留默认分配器。
"#
    }
}

// ============================================================================
// 2. StartupTimeOptimization — 启动时间优化
// ============================================================================

/// 启动时间优化策略
/// time optimization strategy
pub struct StartupTimeOptimization;

impl StartupTimeOptimization {
    /// 启动时间优化总览
    /// time optimization
    pub fn overview() -> &'static str {
        r#"=== WASM 启动时间优化 ===

1. 减少 JS 胶水代码
   - 使用 `wasm-bindgen` 的 `--target web` 生成 ES 模块，减少 polyfill
   - 避免不必要的 `js-sys` / `web-sys` feature
   - 使用 `wasm-pack` 的 `--mode no-install` 跳过 npm 包安装

2. 延迟初始化（Lazy Initialization）
   - 将非关键路径的初始化推迟到首次使用时
   - 使用 `LazyLock` / `once_cell::Lazy` 替代立即初始化
   - 拆分大型静态数据为按需加载的 chunk

3. 模块分割与流式编译
   - 利用 WebAssembly.instantiateStreaming 实现边下载边编译
   - 将应用拆分为核心模块 + 功能模块，按需动态加载

4. 避免阻塞主线程
   - 使用 Web Worker 执行 WASM 初始化
   - 大型计算任务通过 `postMessage` offload 到 Worker
"#
    }

    /// 减少 JS 胶水代码
    /// JS
    pub fn reduce_js_glue() -> &'static str {
        r#"=== 减少 JS 胶水代码 ===

JS 胶水代码体积来源：
- wasm-bindgen 生成的适配层（类型转换、内存管理）
- web-sys 的庞大 API 绑定表
- js-sys 的 JavaScript 全局对象封装

优化手段：
1. 精确启用 web-sys feature
   ```toml
   web-sys = { version = "0.3", features = ["console", "Window"] }
   ```

2. 使用 `--weak-refs` 和 `--reference-types`
   - 减少手动 JS 对象生命周期管理代码
   - 需要浏览器支持 Reference Types proposal

3. 自定义最小化绑定
   - 仅绑定需要的函数，而非整个 crate
   - 手写 `extern "C"` 替代 web-sys 大模块
"#
    }

    /// 延迟初始化
    /// 延迟Initialize
    pub fn lazy_initialization() -> &'static str {
        r#"=== 延迟初始化 ===

Rust 侧延迟初始化：
```rust
use std::sync::LazyLock;

static CONFIG: LazyLock<Config> = LazyLock::new(|| {
    Config::load_from_env()
});
```

JS 侧延迟加载：
```javascript
// 仅在需要时加载 WASM 模块
async function getWasmModule() {
    if (!wasmModule) {
        wasmModule = await import('./pkg/my_wasm.js');
    }
    return wasmModule;
}
```

优势：
- 首屏加载时间显著降低
- 内存占用更平缓
- 对单页应用（SPA）尤其有效
"#
    }
}

// ============================================================================
// 3. JsWasmBoundaryOverhead — JS ↔ WASM 边界调用开销
// ============================================================================

/// JS ↔ WASM 边界调用开销分析
/// JS ↔ WASM edge overhead analyze
pub struct JsWasmBoundaryOverhead;

impl JsWasmBoundaryOverhead {
    /// 边界调用开销总览
    /// edge overhead
    pub fn overview() -> &'static str {
        r#"=== JS ↔ WASM 边界调用开销 ===

调用类型与开销：

1. WASM 导出函数（JS 调用 WASM）
   - 基础开销：约 10-30ns（现代引擎）
   - 参数传递：整数/浮点直接通过寄存器，零开销
   - 字符串/数组：需要内存拷贝（WASM 线性内存 <-> JS Heap）

2. WASM 导入函数（WASM 调用 JS）
   - 开销更高：约 30-100ns（涉及 JS 引擎状态切换）
   - 频繁调用会显著影响性能

3. Promises / async
   - 异步边界涉及事件循环调度
   - 额外开销：微任务队列、Promise 状态管理

优化建议：
- 批量处理：在 WASM 内部完成尽可能多的工作，减少边界穿越次数
- 使用 TypedArray 共享内存，避免数据拷贝
- 避免在热循环中频繁调用 JS 回调
"#
    }

    /// 调用类型对比
    /// type to
    pub fn call_types() -> &'static str {
        r#"=== 调用类型开销对比 ===

| 调用方向          | 典型开销 | 主要成本来源                 |
|-------------------|----------|-----------------------------|
| JS -> WASM (简单) | 10-30ns  | 栈帧建立、类型检查            |
| JS -> WASM (传参) | 30-100ns | 线性内存访问、字符串编码转换  |
| WASM -> JS        | 30-100ns | JS 引擎进入、GC 安全点        |
| WASM -> JS (DOM)  | 50-200ns | DOM API 封装、渲染队列同步    |

关键原则：
- 最小化边界穿越次数
- 在边界处进行数据打包/解包，而非逐字段传递
- 优先使用 WASM 内部计算，JS 仅负责 I/O 和渲染
"#
    }

    /// 缓解策略
    /// strategy
    /// 缓解strategy
    pub fn mitigation() -> &'static str {
        r#"=== 缓解边界开销的策略 ===

1. 批处理 API 设计
   - 设计接受数组/批量输入的 WASM 函数
   - 一次调用处理 N 个元素，而非 N 次调用处理 1 个

2. 共享内存模式
   - JS 和 WASM 通过 SharedArrayBuffer 协作
   - 使用 Atomics 进行同步，避免重复拷贝

3. 减少动态分配
   - 在 WASM 内部分配输出缓冲区，返回指针+长度
   - JS 使用 `new Uint8Array(wasm.memory.buffer, ptr, len)` 视图访问

4. 内联小型 JS 函数
   - 如果 JS 函数足够小，引擎可能内联优化
   - 减少调用栈深度
"#
    }
}

// ============================================================================
// 4. BuildToolComparison — wasm-bindgen vs wasm-pack
// ============================================================================

/// wasm-bindgen vs wasm-pack 构建选项对比
/// wasm-bindgen vs wasm-pack 构建选项to比
pub struct BuildToolComparison;

impl BuildToolComparison {
    /// wasm-bindgen 构建选项
    pub fn wasm_bindgen_options() -> &'static str {
        r#"=== wasm-bindgen 构建选项 ===

wasm-bindgen 是底层绑定生成工具，直接控制输出：

常用选项：
- `--target web`：生成 ES 模块，无 bundler 依赖
- `--target bundler`：生成适合 webpack/rollup 的模块
- `--target nodejs`：生成 CommonJS 模块
- `--weak-refs`：启用 WeakRef 支持，减少手动内存管理
- `--reference-types`：启用 reference types proposal

使用场景：
- 需要精细控制构建流程
- 集成到自定义构建系统（如 Bazel、CMake）
- 与已有 JS 项目深度集成
"#
    }

    /// wasm-pack 构建选项
    /// wasm-pack
    pub fn wasm_pack_options() -> &'static str {
        r#"=== wasm-pack 构建选项 ===

wasm-pack 是面向生态的高级构建工具，封装了 wasm-bindgen 和 wasm-opt：

常用命令：
- `wasm-pack build --release`：生产构建（自动优化）
- `wasm-pack build --dev`：开发构建（快速编译）
- `wasm-pack build --target web`：浏览器目标
- `wasm-pack build --target nodejs`：Node.js 目标
- `wasm-pack build --no-typescript`：不生成 .d.ts

额外能力：
- 自动调用 wasm-opt
- 生成 package.json
- 支持发布到 npm registry
- 内置 webpack/rollup 模板

使用场景：
- 快速开始 WASM 项目
- 发布 WASM 库到 npm
- 不需要深度定制构建流程
"#
    }

    /// 对比总结
    /// to summary
    /// to比summary
    pub fn comparison() -> &'static str {
        r#"=== wasm-bindgen vs wasm-pack 对比 ===

| 维度         | wasm-bindgen               | wasm-pack                  |
|--------------|----------------------------|----------------------------|
| 定位         | 底层绑定生成器              | 高层构建与发布工具          |
| 配置复杂度   | 高（需手动处理所有步骤）    | 低（开箱即用）              |
| 优化集成     | 需手动调用 wasm-opt         | 自动调用                    |
| npm 发布     | 需手动配置                  | 内置支持                    |
| 灵活性       | 极高                        | 中等                        |
| 学习曲线     | 陡峭                        | 平缓                        |

选型建议：
- 快速原型 / 发布到 npm → wasm-pack
- 深度集成 / 自定义构建链 → wasm-bindgen + 手动配置
- 大多数项目：先用 wasm-pack，遇到瓶颈再切换到 wasm-bindgen
"#
    }
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binary_size_overview() {
        let doc = BinarySizeOptimization::overview();
        assert!(doc.contains("wasm-opt"));
        assert!(doc.contains("wee_alloc"));
    }

    #[test]
    fn test_wasm_opt_doc() {
        let doc = BinarySizeOptimization::wasm_opt();
        assert!(doc.contains("Binaryen"));
    }

    #[test]
    fn test_wee_alloc_doc() {
        let doc = BinarySizeOptimization::wee_alloc_concept();
        assert!(doc.contains("wee_alloc"));
    }

    #[test]
    fn test_startup_time_overview() {
        let doc = StartupTimeOptimization::overview();
        assert!(doc.contains("延迟初始化"));
    }

    #[test]
    fn test_js_wasm_boundary_overhead() {
        let doc = JsWasmBoundaryOverhead::overview();
        assert!(doc.contains("WASM 导出函数"));
    }

    #[test]
    fn test_call_types_doc() {
        let doc = JsWasmBoundaryOverhead::call_types();
        assert!(doc.contains("JS -> WASM"));
    }

    #[test]
    fn test_mitigation_doc() {
        let doc = JsWasmBoundaryOverhead::mitigation();
        assert!(doc.contains("批处理"));
    }

    #[test]
    fn test_build_tool_comparison() {
        let doc = BuildToolComparison::comparison();
        assert!(doc.contains("wasm-bindgen"));
        assert!(doc.contains("wasm-pack"));
    }

    #[test]
    fn test_wasm_bindgen_options() {
        let doc = BuildToolComparison::wasm_bindgen_options();
        assert!(doc.contains("--target web"));
    }

    #[test]
    fn test_wasm_pack_options() {
        let doc = BuildToolComparison::wasm_pack_options();
        assert!(doc.contains("--release"));
    }
}
