> **Canonical 说明**: 本文件专注 **ort ONNX Runtime Rust 绑定的 Session/Tensor/ExecutionProvider 架构**。
>
> 若只需要使用指南与生态定位，请优先参考：
>
> - [机器学习生态](../../../../concept/06_ecosystem/11_domain_applications/46_machine_learning_ecosystem.md)
>
> 本文件保留架构级深度内容，与上述使用指南形成互补。
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **状态**: ✅ 已完成
>
> **概念族**: Crate 架构 / ort
>
> **层级**: L3-L5

---

# ort Crate 架构解构 {#ort-crate-架构解构}

> **EN**: Ort Architecture
> **Summary**: ort Crate 架构解构 Ort Architecture.
> **最后更新**: 2026-06-29
>
> **内容分级**: [归档级]
>
> **分级**: [B]
>
> **Bloom 层级**: L3-L5 (应用/分析/评价)
>
> **知识领域**: ONNX Runtime、机器学习推理、FFI 封装、硬件加速、异步（Async）/同步执行
>
> **对应 Rust 版本**: 1.96.1+ (ort 2.0.0-rc.12+)

---

## 1. 引言：ort 的生态定位 {#1-引言ort-的生态定位}

> **[来源: [ort crates.io](https://crates.io/crates/ort)]**

`ort` 是 Rust 生态中对接 **Microsoft ONNX Runtime** 的工业级安全封装。
ONNX Runtime 是跨平台、高性能的机器学习推理引擎，支持 CPU、CUDA、TensorRT、OpenVINO、DirectML、CoreML 等执行后端。
`ort` 通过安全的 Rust API 暴露 ONNX Runtime 的会话管理、张量输入输出、执行提供者（Execution Provider）与 IO 绑定能力，广泛应用于图像识别、NLP、语音、推荐系统等场景。

> [来源: [ort 官方文档](https://ort.pyke.io/)]

与纯 Rust 推理引擎（如 `tract`）相比，`ort` 的核心取舍是：

| 维度 | 设计选择 | 工程价值 |
|:--|:--|:--|
| **后端能力** | 绑定 C/C++ ONNX Runtime，复用成熟内核 | 支持最全的 ONNX 算子与硬件加速后端 |
| **封装策略** | 安全 Rust API + `ort_sys` FFI | 隐藏 `unsafe` 细节，保留零成本抽象（Zero-Cost Abstraction） |
| **执行模式** | 同步 `Session::run` 为主，支持异步（Async）回调 | 与 Rust 同步/异步生态均可集成 |
| **部署形态** | 可静态链接或动态加载 `onnxruntime` 动态库 | 灵活控制二进制体积与授权合规 |
| **类型安全** | `Tensor<T>` / `DynValue` / `SessionInputs` | 编译期区分张量类型与输入名称 |

> [来源: [ort GitHub Repository](https://github.com/pykeio/ort)]

```rust,ignore
use ort::session::{builder::GraphOptimizationLevel, Session};
use ort::Tensor;

let mut session = Session::builder()?
    .with_optimization_level(GraphOptimizationLevel::Level3)?
    .with_intra_threads(4)?
    .commit_from_file("model.onnx")?;

let input = Tensor::from_array(([1usize, 1, 1, 1], vec![1.0_f32].into_boxed_slice()))?;
let outputs = session.run(ort::inputs![input])?;
let (_shape, data) = outputs[0].try_extract_tensor::<f32>()?;
```

> [来源: [ort docs.rs – Session](https://docs.rs/ort/latest/ort/session/struct.Session.html)]

---

## 2. 核心 API 与概念 {#2-核心-api-与概念}

> **[来源: [ONNX Runtime 官方文档](https://onnxruntime.ai/docs/)]**

`ort` 的编程模型围绕以下核心抽象展开：`Environment`、`Session`、`Value`/`Tensor`、`ExecutionProvider`、`IoBinding`。

| 概念 | 说明 | 在 ort 中的对应 |
|:--|:--|:--|
| **Environment** | 进程级全局配置与日志上下文 | `ort::init()` / 隐式默认环境 |
| **Session** | 加载并优化后的 ONNX 模型实例 | `Session::builder()` → `commit_from_file` |
| **Tensor** | 类型化张量输入/输出 | `Tensor::<f32>::from_array(...)` |
| **DynValue** | 类型擦除的运行时（Runtime）值 | `SessionOutputs` 元素、`DynTensor` |
| **ExecutionProvider** | 硬件加速后端（CUDA、TensorRT 等） | `CUDAExecutionProvider::default()` |
| **IoBinding** | 预绑定输入/输出设备内存 | `Session::create_binding(...)` |

> [来源: [ort docs.rs – Value](https://docs.rs/ort/latest/ort/value/struct.Value.html)]

### 2.1 Session 构建流水线 {#21-session-构建流水线}

`Session::builder()` 返回一个类型状态构建器，可链式配置优化级别、线程数、执行提供者、内存分配器等，最终通过 `commit_from_file` 或 `commit_from_memory` 生成 `Session`。

```rust,ignore
use ort::session::builder::GraphOptimizationLevel;

let session = Session::builder()?
    .with_optimization_level(GraphOptimizationLevel::Level3)?
    .with_intra_threads(4)?
    .with_execution_providers([CUDAExecutionProvider::default().build()])?
    .commit_from_file("yolov8m.onnx")?;
```

> [来源: [ort docs.rs – GraphOptimizationLevel](https://docs.rs/ort/latest/ort/session/builder/enum.GraphOptimizationLevel.html)]

### 2.2 张量输入输出 {#22-张量输入输出}

`Tensor::from_array` 支持从 `ndarray::Array` 或 `(shape, data)` 元组构造张量。`Session::run` 返回的 `SessionOutputs` 可通过索引或名称访问，使用 `try_extract_tensor` / `try_extract_array` 获取底层数据。

```rust,ignore
let input = Tensor::from_array(([1usize, 3, 224, 224], vec![0.0_f32; 3 * 224 * 224].into_boxed_slice()))?;
let outputs = session.run(ort::inputs!["image" => input])?;
let (_shape, data) = outputs["output0"].try_extract_tensor::<f32>()?;
```

> [来源: [ort docs.rs – Tensor](https://docs.rs/ort/latest/ort/value/struct.Tensor.html)]

### 2.3 执行提供者（Execution Provider） {#23-执行提供者execution-provider}

执行提供者允许将算子下推到 GPU/NPU 等硬件。`ort` 通过 feature 控制 EP 编译（如 `cuda`、`tensorrt`、`coreml`），运行时通过 `with_execution_providers` 启用。

| EP | 适用平台 | 典型场景 |
|:--|:--|:--|
| CPU | 全平台 | 默认回退、跨平台部署 |
| CUDA | NVIDIA GPU | 通用 GPU 推理 |
| TensorRT | NVIDIA GPU | 低延迟生产推理 |
| OpenVINO | Intel CPU/GPU/NPU | 边缘与 Intel 设备 |
| DirectML | Windows | Windows 桌面/服务器 GPU |
| CoreML | Apple | iOS/macOS 端侧 |

> [来源: [ONNX Runtime Execution Providers](https://onnxruntime.ai/docs/execution-providers/)]

---

## 3. 反例边界 {#3-反例边界}

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 反例 | 错误表现 | 正确做法 |
|:--|:--|:--|
| 未启用对应 EP feature | 调用 CUDA EP 时编译期或运行时回退到 CPU | 在 `Cargo.toml` 中启用 `ort/cuda` 等 feature 并验证环境 |
| 输入张量形状/类型与模型不匹配 | `Session::run` 返回输入形状错误 | 通过模型工具查看输入 metadata，使用 `Tensor::from_array` 精确构造 |
| 跨线程共享可变 `Session` | 编译错误：`Session::run` 需要 `&mut self` | 使用 `Mutex<Session>` 或每个线程持有独立 Session |
| 输出 `DynValue` 生命周期（Lifetimes）误用 | 提取出的张量视图在 `SessionOutputs` drop 后失效 | 在 `outputs` 存活期间使用视图，必要时拷贝数据 |
| 忽略 `commit_from_file` 的模型路径验证 | 生产环境加载错误模型文件 | 校验模型哈希/签名，使用版本化模型仓库 |
| 动态库版本不匹配 | 运行时符号错误、崩溃 | 使用 `ort` 对应版本的预编译二进制或静态链接 |
| 在 `no_std` 环境误用默认 feature | 编译失败或体积过大 | 按需关闭 `std`、`download-binaries` 等 feature |

> [来源: [ort GitHub Issues](https://github.com/pykeio/ort/issues)]

---

## 4. 类型系统利用 {#4-类型系统利用}

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

`ort` 通过类型系统（Type System）将 ONNX Runtime 的运行时语义静态化：

| 维度 | API | 类型系统价值 |
|:--|:--|:--|
| 张量元素类型 | `Tensor::<f32>` vs `Tensor::<i64>` | 编译期保证元素类型与模型输入匹配 |
| 类型擦除 | `DynValue` / `DynTensor` | 在输出类型未知时提供安全抽象，提取时做运行时校验 |
| 构建器类型状态 | `SessionBuilder` → `Session` | 未 `commit` 前无法调用 `run`，避免未初始化模型 |
| 输入命名 | `ort::inputs!["name" => tensor]` | 用字符串名称映射到模型输入，减少顺序错误 |
| 线程安全 | `Session::run(&mut self)` | 通过 `&mut` 在编译期防止数据竞争 |

> [来源: [ort API docs](https://docs.rs/ort/latest/ort/)]

---

## 5. 代码示例锚点 {#5-代码示例锚点}

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 示例 | 文件 | 说明 |
|:--|:--|:--|
| 加载 ONNX 模型并执行推理 | [`crates/c08_algorithms/examples/ort_basic_inference.rs`](../../../../crates/c08_algorithms/examples/ort_basic_inference.rs) | 使用 `Session::builder`、`Tensor::from_array` 与 `try_extract_tensor` |

> [来源: [c08_algorithms Crate](https://github.com/rust-lang/rust-lang-learning/tree/main/crates/c08_algorithms)]

---

## 6. 相关架构与延伸阅读 {#6-相关架构与延伸阅读}

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [Tokio 异步运行时架构](06_tokio_architecture.md) — `ort` 异步执行与 Tokio 集成
- [tract 纯 Rust 推理引擎架构](36_tract_architecture.md) — 与 `ort` 的设计对比
- [candle / AI/ML 生态示例](../../../../crates/c08_algorithms/examples/ai_ml_ecosystem_demo.rs) — Rust ML 基础张量操作
- [异步编程模型](../../../../concept/03_advanced/01_async/02_async.md)
- [FFI 与 unsafe 边界](../../../../concept/04_formal/04_model_checking/05_verification_toolchain.md)

---

## 权威来源索引 {#权威来源索引}

> **[来源: [ort crates.io](https://crates.io/crates/ort)]**
>
> **[来源: [ort docs.rs](https://docs.rs/ort/latest/ort/)]**
>
> **[来源: [ort 官方文档](https://ort.pyke.io/)]**
>
> **[来源: [ort GitHub](https://github.com/pykeio/ort)]**
>
> **[来源: [ONNX Runtime 官方文档](https://onnxruntime.ai/docs/)]**
>
> **权威来源**: [ort docs.rs](https://docs.rs/ort/latest/ort/), [ort crates.io](https://crates.io/crates/ort), [ONNX Runtime 官方文档](https://onnxruntime.ai/docs/)
>
> **权威来源对齐变更日志**: 2026-06-29 创建 ort 生态专题，对齐 ort 2.0.0-rc.12 与 ONNX Runtime 官方文档

---

## 权威来源参考 {#权威来源参考}

> **P0（官方/必读）**:
>
> - [来源: [ort Documentation](https://docs.rs/ort/latest/ort/)]
> - [来源: [ort crates.io](https://crates.io/crates/ort)]
> - [来源: [ONNX Runtime 官方文档](https://onnxruntime.ai/docs/)]
> - [来源: [ort 官方教程](https://ort.pyke.io/)]
> **P1（学术论文/演讲）**:
>
> - [来源: [ONNX: Open Neural Network Exchange](https://arxiv.org/abs/2002.06838)] — ONNX 中间表示标准
> - [来源: [TensorRT: Programmable Inference Accelerator](https://arxiv.org/abs/1605.02697)] — GPU 推理加速参考
> **P2（仓库/社区文章）**:
>
> - [来源: [ort GitHub Repository](https://github.com/pykeio/ort)]
> - [来源: [ONNX Runtime GitHub](https://github.com/microsoft/onnxruntime)]
> - [来源: [This Week in Rust](https://this-week-in-rust.org/)]

## 学术权威参考 {#学术权威参考}

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Aeneas](https://aeneas-verification.github.io/)
- [Oxide](https://arxiv.org/abs/1903.00982)
