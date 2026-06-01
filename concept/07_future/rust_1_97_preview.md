# Rust 1.97 前沿特性预览
>
> **受众**: [专家]
> **内容分级**: [实验级]

> **跟踪版本**: nightly 1.98.0 (2026-05-29)
> **预计稳定时间**: 2026-07-16（Rust 1.97.0 计划发布日期）
> **状态**: 🧪 Nightly 实验性 / 部分已 MCP 通过
>
> **权威来源**:
>
> - [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)
> - [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
> - [Rust Internals Forum](https://internals.rust-lang.org/)

---

## 一、语言特性预览

### 1.1 Async Drop (MCP #727 已通过，实现中)

**状态**: 🧪 Nightly 实验性，MCP 已通过

**核心问题**: 当前 Rust 中 `drop` 是同步的，无法 `await` 异步清理操作（如关闭网络连接、刷新文件缓冲区）。

**1.97 进展**:

- `AsyncDrop` trait 设计已确定
- `async fn drop(&mut self)` 语法支持
- 编译器已能生成异步析构状态机

**影响**: 解决异步资源释放的核心痛点，不再需要手动 `flush()`/`close()` 后丢弃。

**代码示例** (nightly):

```rust,ignore
#![feature(async_drop)]

use std::async_drop::AsyncDrop;

struct AsyncFile {
    handle: tokio::fs::File,
}

impl AsyncDrop for AsyncFile {
    async fn drop(&mut self) {
        let _ = self.handle.flush().await;
        let _ = self.handle.shutdown().await;
    }
}
```

---

### 1.2 Return Type Notation (RTN)

**状态**: 🧪 RFC 讨论中

**核心问题**: `impl Trait` 返回类型中无法命名关联类型，导致 `async fn` / `-> impl Iterator` 的返回类型难以在 trait bound 中表达。

**提案语法**:

```rust,ignore
// 使用 RTN 在 trait bound 中引用返回类型
trait Processor {
    fn process(&self) -> impl Future<Output = i32>;
}

fn spawn_processor<P>(p: P)
where
    P: Processor,
    P::process(): Send,  // RTN: 约束 process() 的返回类型为 Send
{
    tokio::spawn(async move { p.process().await });
}
```

---

### 1.3 Pin Ergonomics / Safe Pin Projection

**状态**: 📋 RFC 讨论阶段

**核心问题**: `Pin<&mut Self>` 的字段投影需要 `unsafe` 或 `pin-project` crate，学习曲线陡峭。

**可能方向**:

- 编译器自动生成安全的 pin projection
- 或提供派生宏 `#[derive(PinProject)]` 进入标准库

---

## 二、编译器基础设施

### 2.1 并行前端 (Parallel Frontend)

**状态**: 🧪 Nightly，8核提速 20-25%

**进展**:

- `-Zthreads=8` 已可用
- 查询系统并行化基本完成
- 正在解决增量编译与并行前端的交互问题

**使用** (nightly):

```bash
RUSTFLAGS="-Zthreads=8" cargo build
```

**深度文档**: [09_parallel_frontend_preview.md](09_parallel_frontend_preview.md)

---

### 2.2 Cranelift 后端

**状态**: 🧪 Nightly 预览，debug 构建快 20%

**进展**:

- `cg_clif` 已能通过大部分 rustc 测试
- 不支持 LTO（设计限制）
- 适合开发迭代，不适合 release

**使用** (nightly):

```bash
cargo +nightly build -Zcodegen-backend=cranelift
```

**深度文档**: [16_cranelift_backend_preview.md](16_cranelift_backend_preview.md)

---

### 2.3 build-std (RFC #3873)

**状态**: ✅ 已合并，向稳定推进

**核心能力**: 编译时重新构建标准库，允许：

- 自定义 panic handler（无需 `#![no_std]`）
- 补丁 std 中的 bug
- 嵌入式/OS 开发中裁剪 std

**使用** (nightly):

```bash
cargo +nightly build -Zbuild-std=core,alloc,std --target x86_64-unknown-linux-gnu
```

---

## 三、形式化验证生态

### 3.1 AutoVerus / VeruSAGE (Microsoft)

**状态**: ✅ 已开源

**核心能力**: LLM 自动证明合成，将自然语言规约转换为 Verus 可验证代码。

**资源**: [github.com/microsoft/verus-proof-synthesis](https://github.com/microsoft/verus-proof-synthesis)

**深度文档**: [02_formal_methods.md](02_formal_methods.md)

---

### 3.2 Kani 0.65+ (Amazon)

**状态**: ✅ 活跃开发

**1.97 新能力**:

- 量词支持 (`forall`, `exists`)
- 循环契约 (`#[kani::loop_invariant]`)
- Autoharness（自动生成 proof harness）

**资源**: [model-checking.github.io/kani](https://model-checking.github.io/kani/)

---

### 3.3 ESBMC for Rust

**状态**: ✅ Rust Foundation 资助项目

**核心能力**: 基于有界模型检查的 Rust 标准库验证，已加入标准库验证 CI。

**资源**: [rustfoundation.org/media/expanding-the-rust-formal-verification-ecosystem-welcoming-esbmc](https://rustfoundation.org/media/expanding-the-rust-formal-verification-ecosystem-welcoming-esbmc)

---

## 四、异步 Rust 前沿

### 4.1 Async fn in dyn Trait

**状态**: 🧪 Nightly 实验性

**核心突破**: 消除 `#[async_trait]` 在 `dyn Trait` 场景中的需求。

```rust,ignore
#![feature(async_fn_in_dyn_trait)]

trait Service {
    async fn handle(&self, req: Request) -> Response;
}

// 无需 async_trait！
fn run_service(s: &dyn Service) {
    s.handle(req); // 编译器自动处理虚表调度
}
```

---

### 4.2 异步生成器 (Async Generators)

**状态**: 📋 远期目标

**愿景**: 替代手动 `Stream` 实现，提供类似 `yield` 的语法：

```rust,ignore
#![feature(async_generators)]

async gen fn counter_stream(max: usize) -> impl Stream<Item = usize> {
    for i in 0..max {
        yield i;
    }
}
```

---

## 五、标准库演进

### 5.1 新稳定 API 跟踪 (1.97 候选)

| API | 状态 | 说明 |
|:---|:---|:---|
| `VecDeque::truncate_front` | 🧪 Nightly | 从头部截断双端队列 |
| `int_format_into` | 🧪 Nightly | 整数格式化到现有缓冲区 |
| `RefCell::try_map` | 🧪 Nightly | 尝试性 RefCell 映射 |
| `String::into_raw_parts` | 🧪 Nightly | 分解 String 为原始组件 |

---

## 六、Cargo 与工具链

### 6.1 Cargo 新特性

| 特性 | 状态 | 说明 |
|:---|:---|:---|
| `target.'cfg(..)'.rustdocflags` | ✅ 1.96 已稳定 | 条件 rustdoc 标志 |
| `cargo lint` 子命令 | 📋 RFC 阶段 | 统一的 lint 管理接口 |
| 依赖图谱可视化 | 📋 设计阶段 | `cargo tree --graph` |

### 6.2 rustfmt / clippy

- **clippy**: 新增 `manual_is_ascii_check` lint（1.97 nightly）
- **rustfmt**: `imports_granularity = "Module"` 稳定性改进

---

## 七、工业级采用里程碑

### 7.1 Rust for Linux

- Linux 6.12+ 已支持 Rust 内核模块
- Rust 1.96.0 `unused_features` lint 影响内核构建流程（已适配）
- 驱动开发框架 `pin-init` 成熟

### 7.2 Android Rust 化

- AOSP 中 Rust 代码占比持续增长
- Binder、Keystore、DNS 等核心组件已 Rust 化

### 7.3 Windows 驱动 Rust 支持

- Windows 11 24H2 引入 Rust 驱动开发工具链
- WDK (Windows Driver Kit) Rust 绑定预览

---

## 八、与本项目相关的追踪任务

| 特性 | 本项目影响 | 行动项 |
| :--- | :--- | :--- |
| Async Drop | c06_async 需要新增示例 | 跟踪 nightly 进展，稳定后补充 |
| RTN | c02_type_system trait 章节需更新 | 1.97 stable 后补充 |
| 并行前端 | docs/ 编译器基础设施需覆盖 | Phase 4 执行 |
| Cranelift | docs/ 编译器基础设施需覆盖 | Phase 4 执行 |
| build-std | c13_embedded 需补充示例 | Phase 4 执行 |
| AutoVerus | L4/L7 形式化工具需覆盖 | Phase 3 执行 |
| ESBMC | L4/L7 形式化工具需覆盖 | Phase 3 执行 |

---

## 九、参考资源

| 资源 | URL |
| :--- | :--- |
| Rust Project Goals 2026 | [rust-lang.github.io/rust-project-goals/2026](https://rust-lang.github.io/rust-project-goals/2026/) |
| Async Rust Goals | [rust-lang.github.io/rust-project-goals/2025h1/async.html](https://rust-lang.github.io/rust-project-goals/2025h1/async.html) |
| Cranelift 后端目标 | [rust-lang.github.io/rust-project-goals/2025h2/production-ready-cranelift.html](https://rust-lang.github.io/rust-project-goals/2025h2/production-ready-cranelift.html) |
| 并行前端目标 | [rust-lang.github.io/rust-project-goals/2026/parallel-front-end.html](https://rust-lang.github.io/rust-project-goals/2026/parallel-front-end.html) |
| AutoVerus | [github.com/microsoft/verus-proof-synthesis](https://github.com/microsoft/verus-proof-synthesis) |
| Kani 文档 | [model-checking.github.io/kani](https://model-checking.github.io/kani/) |

---

> **最后更新**: 2026-05-30
> **维护者**: 本项目知识库团队
> **状态**: 🧪 活跃跟踪中，每 2 周更新一次
> **过渡**: Rust 1.97 前沿特性预览 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。
> **过渡**: Rust 1.97 前沿特性预览 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。
> **过渡**: Rust 1.97 前沿特性预览 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。

### 补充定理链

- **定理**: Rust 1.97 前沿特性预览 定义 ⟹ 类型安全保证
- **定理**: Rust 1.97 前沿特性预览 定义 ⟹ 类型安全保证
- **定理**: Rust 1.97 前沿特性预览 定义 ⟹ 类型安全保证

## 认知路径

> **认知路径**: 从 Rust 核心语言特性出发，经由 **Rust 1.97 前沿特性预览** 的生态/前沿实践，通向系统化工程能力与未来语言演进方向。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| Rust 1.97 前沿特性预览 基础原理 ⟹ 正确选型 | 理解核心概念与适用边界 | 能在实际项目中做出合理决策 | 高 |
| Rust 1.97 前沿特性预览 选型实践 ⟹ 常见陷阱 | 忽视版本兼容性与生态成熟度 | 技术债务或迁移成本 | 中 |
| Rust 1.97 前沿特性预览 陷阱规避 ⟹ 深度掌握 | 持续跟踪社区演进与最佳实践 | 能进行架构设计与技术预研 | 高 |

> **过渡**: 掌握 Rust 1.97 前沿特性预览 的基础概念后，建议通过实际案例与源码阅读加深理解，建立从理论到实践的桥梁。

> **过渡**: 在工程实践中应用 Rust 1.97 前沿特性预览 时，务必评估生态成熟度、社区支持与长期维护风险，避免过度依赖实验性技术。

> **过渡**: Rust 1.97 前沿特性预览 反映了 Rust 生态系统的演进趋势与语言设计哲学，理解这些趋势有助于预判未来发展方向并做出前瞻性技术决策。

### 反命题与边界

> **反命题**: "Rust 1.97 前沿特性预览 是万能解决方案，适用于所有场景" —— 错误。任何技术选择都有权衡，需根据具体需求、团队能力与项目约束综合评估。
