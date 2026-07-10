> **Canonical 说明**: 本文件专注 **tract 纯 Rust 推理引擎的类型化计算图与 SimplePlan 架构**。
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
> **概念族**: Crate 架构 / tract
>
> **层级**: L3-L5

---

# tract Crate 架构解构 {#tract-crate-架构解构}

> **EN**: Tract Architecture
> **Summary**: tract Crate 架构解构 Tract Architecture.
> **最后更新**: 2026-06-29
>
> **内容分级**: [归档级]
>
> **分级**: [B]
>
> **Bloom 层级**: L3-L5
>
> **知识领域**: 纯 Rust 推理引擎、ONNX/TensorFlow Lite、模型优化、端侧部署
>
> **对应 Rust 版本**: 1.97.0+ (Edition 2024)

---

## 1. 引言：tract 的生态定位 {#1-引言tract-的生态定位}

> **[来源: [tract-onnx crates.io](https://crates.io/crates/tract-onnx)]**

`tract` 是 Sonos 开源的 **纯 Rust 神经网络推理引擎**，主打“Tiny, no-nonsense, self contained”。它无需外部 C/C++ 运行时（Runtime）即可加载并执行 ONNX、TensorFlow、TensorFlow Lite 与 NNEF 模型，特别适合对二进制体积、跨平台构建和依赖审计敏感的场景，如嵌入式、可信执行环境（TEE）与端侧 AI。

> [来源: [tract docs.rs](https://docs.rs/tract-onnx/latest/tract_onnx/)]

与 `ort` 等 ONNX Runtime 封装相比，`tract` 的核心取舍是：

| 维度 | 设计选择 | 工程价值 |
|:--|:--|:--|
| **实现语言** | 纯 Rust，零外部动态库 | 跨平台构建友好、可审计、适合 `no_std` 受限环境 |
| **后端范围** | 主要 CPU 推理 | 体积小、启动快，但缺少 GPU/NPU 高级后端 |
| **模型格式** | ONNX / TensorFlow / TFLite / NNEF | 统一抽象覆盖主流训练框架导出格式 |
| **优化策略** | 常量折叠、算子融合、量化（INT8） | 在编译期/加载期完成图优化 |
| **类型抽象** | `TypedModel` / `SimplePlan` / `Tensor` | 用 Rust 类型表达静态图与执行计划 |

> [来源: [tract GitHub Repository](https://github.com/snipsco/tract)]

```rust,ignore
use tract_onnx::prelude::*;

let model = tract_onnx::onnx()
    .model_for_path("model.onnx")?
    .into_optimized()?
    .into_runnable()?;

let input = Tensor::zero::<f32>(&[1, 1, 1, 1])?;
let outputs = model.run(tvec![input])?;
let view = outputs[0].to_array_view::<f32>()?;
println!("output shape = {:?}", view.shape());
```

> [来源: [tract-onnx examples](https://github.com/snipsco/tract/tree/main/examples)]

---

## 2. 核心 API 与概念 {#2-核心-api-与概念}

> **[来源: [tract-core docs.rs](https://docs.rs/tract-core/latest/tract_core/)]**

`tract` 的编程模型围绕以下核心抽象展开：`Onnx` / `Tensorflow` 导入器、`TypedModel`、`SimplePlan`、`Tensor`、`TVec` 与 `Fact`。

| 概念 | 说明 | 在 tract 中的对应 |
|:--|:--|:--|
| **模型导入器** | 将外部格式解析为 tract 内部图 | `tract_onnx::onnx()` / `tract_tensorflow::tensorflow()` |
| **TypedModel** | 类型化的计算图，包含算子与数据流 | `model_for_path(...)` 返回的模型对象 |
| **SimplePlan** | 优化后的执行计划 | `.into_optimized()?.into_runnable()?` |
| **Fact** | 张量形状与元素类型的声明 | `f32::fact(&[3])` / `TypedFact::dt_shape(...)` |
| **Tensor** | 运行时张量值 | `Tensor::zero::<f32>(...)` / `tensor1(&[...])` |
| **TVec** | 小型向量优化容器 | `tvec![tensor]` 作为算子输入 |

> [来源: [tract-onnx prelude docs](https://docs.rs/tract-onnx/latest/tract_onnx/prelude/index.html)]

### 2.1 模型加载与优化流水线 {#21-模型加载与优化流水线}

`tract` 将模型生命周期（Lifetimes）显式分为解析、优化、可运行三个阶段。开发者可在中间阶段检查或修改图，例如插入量化、裁剪子图、查看中间形状。

```rust,ignore
let model = tract_onnx::onnx()
    .model_for_path("model.onnx")?      // 1. 解析 ONNX 图
    .into_optimized()?                   // 2. 常量折叠、算子融合等优化
    .into_runnable()?;                   // 3. 生成可执行计划
```

> [来源: [tract docs.rs – Onnx](https://docs.rs/tract-onnx/latest/tract_onnx/struct.Onnx.html)]

### 2.2 程序化构造计算图 {#22-程序化构造计算图}

除了加载外部模型，`tract_core` 还允许用 Rust 代码直接构造 `TypedModel`。这对单元测试、自定义算子验证和教学非常有用。

```rust,ignore
use tract_onnx::prelude::*;

let mut model = TypedModel::default();
let input_fact = f32::fact(&[3]);
let input = model.add_source("input", input_fact)?;
let three = model.add_const("three", tensor1(&[3.0f32]))?;
let add = model.wire_node(
    "add",
    tract_onnx::tract_core::ops::math::add::bin_typed(),
    &[input, three],
)?;
model.auto_outputs()?;

let plan = SimplePlan::new(&model)?;
let outputs = plan.run(tvec![tensor1(&[1.0f32, 2.0, 3.0]).into()])?;
```

> [来源: [tract-core examples](https://docs.rs/tract-core/latest/tract_core/index.html)]

### 2.3 量化与体积优化 {#23-量化与体积优化}

`tract` 内置对 INT8/QU8 量化图的支持，并能在加载期完成权重布局转换。配合 `cargo` 的 `opt-level = z`/`strip`，可生成极小的端侧推理二进制。

> [来源: [tract quantization docs](https://github.com/snipsco/tract/tree/main/doc)]

---

## 3. 反例边界 {#3-反例边界}

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 反例 | 错误表现 | 正确做法 |
|:--|:--|:--|
| 跳过 `.into_optimized()` 直接运行 | 推理性能显著下降 | 始终调用图优化流水线 |
| 输入形状与模型 Fact 不匹配 | `run` 时 panic 或形状错误 | 用 `model.input_fact(0)?` 校验期望形状 |
| 在热路径重复加载模型 | 启动延迟高、内存浪费 | 缓存 `RunnableModel`，复用执行计划 |
| 误用 `tensor1` 维度 | 一维张量输入给需要 NCHW 的 CNN | 根据模型输入 Fact 构造对应维度张量 |
| 忽视算子支持清单 | 加载失败：不支持的 ONNX 算子 | 事先用 `tract` 工具验证模型兼容性 |
| 在需要确定性的场景使用动态 batch | 延迟抖动、内存分配不可预测 | 固定 batch 维度或使用 `pulse` 扩展 |
| 把 `tract` 用于需要 GPU 的大规模 serving | 吞吐受限 | 评估 `ort` 或专用 serving 框架 |

> [来源: [tract GitHub Issues](https://github.com/snipsco/tract/issues)]

---

## 4. 类型系统利用 {#4-类型系统利用}

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

`tract` 通过类型系统（Type System）将神经网络图的静态结构表达在编译期：

| 维度 | API | 类型系统价值 |
|:--|:--|:--|
| 图类型化 | `TypedModel` vs `InferenceModel` | 区分已确定形状的类型化图与待推导图 |
| 执行计划不可变 | `SimplePlan` | 计划生成后不可修改，保证运行时行为稳定 |
| 张量元素类型 | `Tensor::zero::<f32>` / `to_array_view::<f32>` | 提取时编译期指定元素类型 |
| 输入容器 | `TVec<Tensor>` | 小型内联优化，避免堆分配 |
| 错误传递 | `TractResult<T>` | 将加载、优化、运行错误统一为 Result |

> [来源: [tract-core API docs](https://docs.rs/tract-core/latest/tract_core/)]

---

## 5. 代码示例锚点 {#5-代码示例锚点}

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 示例 | 文件 | 说明 |
|:--|:--|:--|
| 加载 ONNX 模型并执行纯 Rust 推理 | [`crates/c08_algorithms/examples/tract_basic_inference.rs`](../../../../crates/c08_algorithms/examples/tract_basic_inference.rs) | 使用 `tract_onnx::onnx()`、`into_optimized`、`into_runnable` |

> [来源: [c08_algorithms Crate](https://github.com/rust-lang/rust-lang-learning/tree/main/crates/c08_algorithms)]

---

## 6. 相关架构与延伸阅读 {#6-相关架构与延伸阅读}

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [ort ONNX Runtime Rust 架构](35_ort_architecture.md) — 与 `tract` 的 FFI vs 纯 Rust 对比
- [candle / AI/ML 生态示例](../../../../crates/c08_algorithms/examples/ai_ml_ecosystem_demo.rs) — Rust ML 张量基础
- [嵌入式与 FFI 模式](../../../../concept/04_formal/04_model_checking/05_verification_toolchain.md)
- [设计模式：策略模式](../../../../concept/06_ecosystem/03_design_patterns/02_patterns.md)

---

## 权威来源索引 {#权威来源索引}

> **[来源: [tract-onnx crates.io](https://crates.io/crates/tract-onnx)]**
>
> **[来源: [tract-onnx docs.rs](https://docs.rs/tract-onnx/latest/tract_onnx/)]**
>
> **[来源: [tract GitHub](https://github.com/snipsco/tract)]**
>
> **[来源: [ONNX 规范](https://onnx.ai/onnx/intro/)]**
>
> **权威来源**: [tract-onnx docs.rs](https://docs.rs/tract-onnx/latest/tract_onnx/), [tract-onnx crates.io](https://crates.io/crates/tract-onnx), [tract GitHub](https://github.com/snipsco/tract)
>
> **权威来源对齐变更日志**: 2026-06-29 创建 tract 生态专题，对齐 tract-onnx 0.23.1 与 ONNX 官方规范

---

## 权威来源参考 {#权威来源参考}

> **P0（官方/必读）**:
>
> - [来源: [tract-onnx Documentation](https://docs.rs/tract-onnx/latest/tract_onnx/)]
> - [来源: [tract-onnx crates.io](https://crates.io/crates/tract-onnx)]
> - [来源: [tract GitHub Repository](https://github.com/snipsco/tract)]
> - [来源: [ONNX 规范](https://onnx.ai/onnx/intro/)]
> **P1（学术论文/演讲）**:
>
> - [来源: [ONNX: Open Neural Network Exchange](https://arxiv.org/abs/2002.06838)] — ONNX 中间表示标准
> - [来源: [Quantization and Training of Neural Networks for Efficient Integer-Arithmetic-Only Inference](https://arxiv.org/abs/1712.05877)] — INT8 量化参考
> **P2（仓库/社区文章）**:
>
> - [来源: [tract examples](https://github.com/snipsco/tract/tree/main/examples)]
> - [来源: [This Week in Rust](https://this-week-in-rust.org/)]

## 学术权威参考 {#学术权威参考}

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Aeneas](https://aeneas-verification.github.io/)
- [Oxide](https://arxiv.org/abs/1903.00982)
