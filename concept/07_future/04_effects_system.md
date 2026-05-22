# Effects System: Concept Pre-study（效果系统：概念预研）

> **层级**: L7 前沿趋势
> **定位**: 本文件是 Rust 效果系统（Effect System）的**概念预研**，跟踪类型系统向显式效果追踪演进的理论动向与工程实践。内容具有推测性，随语言团队决策动态更新。
> **前置概念**: [Async](../03_advanced/02_async.md) · [Traits](../02_intermediate/01_traits.md) · [Generics](../02_intermediate/02_generics.md) · [Type Theory](../04_formal/02_type_theory.md)
> **主要来源**: [Koka] · [Eff] · [Haskell GHC] · [Rust Lang Team Blog] · [类型理论研究]

---

> **Bloom 层级**: 分析 → 评价
**变更日志**:

- v1.0 (2026-05-13): 初始版本。建立 Effect 系统概念框架、Rust 现有 effect 映射、AsyncFn 作为原型、跨语言对比、演进路线图
$entry

---

## 〇、Effect System 概念全景

```mermaid
mindmap
  root((Effect System<br/>效果系统))
    理论基础
      代数效应[代数效应<br/>Plotkin & Pretnar 2009]
      类型效应[类型效应<br/>标记集合 + 传播检查]
      效果多态[效果多态<br/>e 效果变量]
    Rust 现有实现
      async[async → Future 状态机<br/>效果: 异步挂起]
      unsafe[unsafe → 安全边界标记<br/>效果: 放弃编译器保证]
      const_fn[const fn → 编译期求值<br/>效果: 无副作用]
      Result[Result<T,E> → 异常效果<br/>效果: 可失败]
      Send[Send/Sync → 线程安全<br/>效果: 并发约束]
    跨语言模型
      Koka[Koka<br/>完整代数效应 + 处理器]
      Eff[Eff<br/>代数效应 + 子类型]
      Haskell[Haskell<br/>Monad 变换器]
      Java[Java<br/>Checked Exceptions]
      Rust当前[Rust 当前<br/>关键字 + Trait]
      Rust理想[Rust 理想<br/>统一 effect 关键字]
    演进方向
      AsyncFn[AsyncFn<br/>效果多态原型]
      gen_blocks[gen blocks<br/>同步协程效果]
      effect_keyword[统一 effect 关键字<br/>远期方向]
      backward_compat[向后兼容挑战<br/>Edition 迁移]
```

> **认知功能**: 此 mindmap 构建 Effect System 的全局认知脚手架。**功能定位**: 将分散的效果机制（async/unsafe/const/Result/Send）整合为"理论-实现-对比-演进"四维分析框架。**使用建议**: 按背景选择入口——类型论背景从"理论基础"切入，工程背景从"Rust 现有实现"切入，策略背景从"演进方向"切入。**关键洞察**: Rust 当前的效果表达是碎片化的（各关键字独立运作），向统一 effect 关键字演进是消除碎片化的长期趋势，最大障碍并非技术可行性，而是向后兼容性与社区共识。[来源: 💡 原创分析]
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

---

## 一、Effect 系统是什么？

> **[来源: Plotkin & Pretnar 2009; Koka Documentation; Wikipedia: Effect System]** ✅

> **[学术来源: Plotkin & Pretnar 2009 — Algebraic Effects; Koka Language]**

**Effect 系统**（Effect System）是将"计算效果"（computational effects）显式编码到类型系统中的理论框架。与类型系统回答"这个函数接受/返回什么值"不同，Effect 系统回答"这个函数在计算过程中**还做了什么**"。

经典效果包括：

| 效果 | 直觉含义 | Rust 当前表达 | 理想的显式表达 |
|:---|:---|:---|:---|
| **IO** | 与外部世界交互 | 无标记 | `fn foo() -> i32 effect Io` |
| **Async** | 可能挂起/恢复 | `async fn` | `fn foo() -> i32 effect Async` |
| **Unsafe** | 可能触发 UB | `unsafe fn` | `fn foo() -> i32 effect Unsafe` |
| **异常** | 可能失败/短路 | `Result` / `?` | `fn foo() -> i32 effect Throws` |
| **非确定性** | 结果不唯一 | 无标记 | `fn foo() -> i32 effect NonDet` |
| **状态** | 修改堆/全局状态 | `&mut T` | `fn foo() -> i32 effect State` |

### 1.2 代数效应（Algebraic Effects）vs 类型效应（Type Effects）

```text
代数效应（Plotkin & Pretnar 2009）:
  ─────────────────────────────────────────
  效果 = 操作签名 + 处理器（handler）
  例: effect State { get(): S; put(s: S): () }
  处理器捕获效果的具体语义（如状态映射到状态单子）
  → 代表语言: Eff, Koka, Flix

类型效应（Rust 方向）:
  ─────────────────────────────────────────
  效果 = 函数类型上的标记集合
  例: fn foo() -> i32 effects {Async, Io}
  编译器检查效果传播，不引入运行时处理器
  → 代表语言: Java checked exceptions（雏形）, Rust（探索中）
```

> **关键区别**: 代数效应强调**效果的处理（handling）**——可以拦截、转换、恢复效果；类型效应强调**效果的追踪（tracking）**——确保调用者知晓被调用函数的所有副作用。Rust 语言团队目前探索的方向更接近**类型效应**，因为引入完整的代数效应处理器会显著增加运行时复杂性和零成本抽象的破坏。

---

## 二、Rust 中的现有 Effect 表达

Rust 尚未引入统一的 `effect` 关键字，但**已经通过不同机制实现了效果的隐性追踪**。

> **[来源: Rust Reference; RFC 3668 AsyncFn; RFC 3762 Const Trait]** ✅

| 效果类别 | 当前 Rust 语法 | 效果语义 | 追踪方式 | 多态支持 |
|:---|:---|:---|:---|:---|
| **异步** | `async fn` | 可能挂起，返回 `Future` | 关键字 + `Future` trait | `AsyncFn` trait (1.85+) |
| **Unsafe** | `unsafe fn` | 可能违反 safety invariant | 关键字 + 调用者义务 | ❌ 无多态 |
| **常量** | `const fn` | 编译期可求值 | 关键字 + MIR const eval | `~const Trait` (unstable) |
| **异常** | `Result<T, E>` + `?` | 可能短路/失败 | 类型承载 + `Try` trait | `?` 自动传播 |
| **泛型约束** | `where T: Send` | 线程安全约束 | Trait bound | 泛型参数多态 |

### 2.2 `async` 作为效果的原型

```rust,ignore
// 当前 Rust: async 是语法关键字，不是类型系统效果
async fn fetch() -> Data { ... }
// 语义: fetch 具有 Async 效果，调用者必须 await

// 理想化效果系统视角:
fn fetch() -> Data effect Async { ... }
// 语义: fetch 的类型签名显式携带 Async 效果
```

`async fn` 的关键设计决策——**效果污染（effect pollution）**：

```text
若 fn foo 调用 async fn bar，则 foo 也必须是 async（或 block_on）
  ↓
效果向上传播：调用者必须处理被调用者的效果
  ↓
这与 checked exceptions 类似：Java 中调用 throws 方法必须 catch 或声明 throws
```

### 2.3 效果状态转换图

```mermaid
stateDiagram-v2
    [*] --> PureFunction: 定义普通函数
    PureFunction --> AsyncContext: 调用 async fn
    PureFunction --> UnsafeContext: 调用 unsafe fn
    PureFunction --> ConstContext: 使用 const fn
    PureFunction --> Throwing: 使用 ? / Result

    AsyncContext --> AsyncPoll: .await / spawn
    AsyncPoll --> [*]: Future 完成
    AsyncContext --> Blocked: block_on
    Blocked --> [*]: 效果消除(同步返回)

    UnsafeContext --> Verified: unsafe {} 块内验证
    Verified --> [*]: 安全边界确认

    ConstContext --> [*]: 编译期求值完成

    Throwing --> Handled: match / ? 传播
    Handled --> [*]: 错误恢复或终止

    note right of AsyncContext
        效果污染:
        调用 async fn 的函数
        自身也携带 Async 效果
    end note

    note right of UnsafeContext
        能力需求:
        调用 unsafe fn 的代码
        必须位于 unsafe {} 块内
    end note
```

> **认知功能**: 此状态图将"效果污染"的抽象概念转化为可视化的状态转换。关键洞察：**效果不是终点，而是需要被处理（poll/await）或消除（block_on）的中间状态**。`async` → `await` → `Future 完成` 的三段式与 `unsafe` → `unsafe {} 验证` → `安全边界确认` 形成对偶——前者是计算挂起效果，后者是安全责任效果。
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

### 2.3 `AsyncFn`：Effect 多态的第一次尝试

> **[来源: RFC 3668; Rust 1.85 Release Notes]**

Rust 1.85 稳定的 `AsyncFn` trait 家族可视为**效果多态（effect polymorphism）**的原型：

```rust,ignore
// AsyncFn: "我不关心这个闭包是否是 async，只要调用时我能 await 结果"
fn call_any<F, T>(f: F) -> impl Future<Output = T>
where
    F: AsyncFn() -> T,  // 效果多态：F 可以是 sync 或 async
{ ... }
```

在效果系统理论中，这对应于：

```text
效果多态签名:
  fn call_any<F>(f: F) where F: Fn() -> T effect e
  // e 是一个效果变量，可以被实例化为 {}（无效果）或 {Async}
```

> **关键洞察**: `AsyncFn` 没有引入完整的 effect 变量语法，而是通过 trait 系统模拟了效果多态。这是 Rust "用类型系统解决问题"设计哲学的延续——不添加新语法，而是用已有机制（trait、关联类型、HRTB）表达新概念。

---

## 三、跨语言对比

> **[来源: Koka; Eff Language; Haskell GHC; Java Exceptions]** ✅

| 语言 | 效果模型 | 表达力 | 运行时成本 | 与 Rust 的关系 |
|:---|:---|:---|:---|:---|
| **Koka** | 代数效应 + 处理器 | ⭐⭐⭐⭐⭐ 完整 | 有（handler 栈） | 理论参考，Rust 不引入运行时处理器 |
| **Eff** | 代数效应 + 子类型 | ⭐⭐⭐⭐⭐ 完整 | 有 | 学术原型 |
| **Haskell** | Monad 变换器 | ⭐⭐⭐⭐ 强 | 有（RTS） | Rust `async` 受 Haskell 启发，但拒绝 Monad |
| **Java** | Checked exceptions | ⭐⭐ 弱 | 零 | Rust 可能借鉴"显式传播"，但拒绝异常机制 |
| **Rust（当前）** | 关键字 + Trait | ⭐⭐⭐ 中 | 零 | 渐进式：async/unsafe/const 各走各的路 |
| **Rust（理想）** | 类型效应 | ⭐⭐⭐⭐ 强 | 零 | 统一语法，保持零成本 |

### 3.2 效果模型谱系图

```mermaid
graph TD
    subgraph 理论基础["效果系统理论谱系"]
        AE[代数效应<br/>Algebraic Effects] --> AE_SIG[操作签名]
        AE --> AE_HANDLER[处理器 Handler]
        TE[类型效应<br/>Type Effects] --> TE_TRACK[效果追踪]
        TE --> TE_PROP[效果传播]
        MONAD[Monad] --> MONAD_BIND[>>= 绑定]
        MONAD --> MONAD_PURE[return 纯值]
    end

    subgraph 语言实现["语言实现映射"]
        AE --> KOKA[Koka<br/>⭐⭐⭐⭐⭐ 完整]
        AE --> EFF[Eff<br/>学术原型]
        MONAD --> HASKELL[Haskell<br/>⭐⭐⭐⭐ 强]
        TE --> JAVA[Java Checked Exceptions<br/>⭐⭐ 弱]
        TE --> RUST_CUR[Rust 当前<br/>关键字 + Trait<br/>⭐⭐⭐ 中]
        TE --> RUST_IDEAL[Rust 理想<br/>统一 effect 关键字<br/>⭐⭐⭐⭐ 强]
    end

    subgraph Rust映射["Rust 现有效果映射"]
        RUST_CUR --> R_ASYNC[async fn<br/>→ Async 效果]
        RUST_CUR --> R_UNSAFE[unsafe fn<br/>→ Unsafe 效果]
        RUST_CUR --> R_CONST[const fn<br/>→ Const 效果]
        RUST_CUR --> R_RESULT[Result<T,E><br/>→ Throws 效果]
        RUST_CUR --> R_SEND[Send/Sync<br/>→ ThreadSafe 效果]
    end

    RUST_IDEAL --> UNIFIED[统一语法<br/>fn foo() -> T effects {Io, Async}]

    style KOKA fill:#e1f5fe
    style HASKELL fill:#e8f5e9
    style RUST_CUR fill:#fff3e0
    style RUST_IDEAL fill:#fce4ec
```

> **认知功能**: 此谱系图揭示 Effect System 的"理论-语言"双层结构。**代数效应**（Koka/Eff）与 **Monad**（Haskell）是两条独立的理论路线，而 **类型效应**（Java/Rust）是工程化的折中方案。Rust 当前处于"类型效应"象限，但正在向"统一语法"方向移动。颜色的深浅提示：浅色为理论原型，暖色为工程实践，粉色为未来方向。
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

### 3.2 为什么 Rust 拒绝 Monad？

```text
Haskell 效果模型:
  IO a = 世界状态 → (a, 世界状态')
  任何 IO 操作都显式传递"世界 token"
  → 纯函数式，但所有效果通过 Monad 组合

Rust 设计哲学冲突:
  1. 零成本抽象: Monad 变换器有运行时成本（即使被优化，语义复杂）
  2. 显式控制: Rust 程序员想要知道每次内存分配和上下文切换
  3.  FFI 兼容: Haskell 的 IO monad 与 C ABI 不直接映射
  4. 学习曲线: Monad 是 Haskell 最大门槛，Rust 有意避免

Rust 的替代方案:
  async/await 语法糖 → 编译为状态机（零运行时开销）
  unsafe 关键字 → 边界标记而非类型变换
  Result<T, E> → 显式错误传播（无隐式异常）
```

---

## 四、对 Rust 类型系统的潜在影响

> **[来源: Rust Internals Discussion; Type Theory Research]** ⚠️ 推测性
的可能性

```rust,ignore
// 推测性语法（非官方，仅供概念讨论）

// 效果声明
effect Async;
effect Io;
effect Unsafe;

// 效果标记函数
fn read_file(path: &str) -> String effects {Io, Async} { ... }

// 效果多态泛型
fn map<T, U, E>(f: impl Fn(T) -> U effects E, xs: Vec<T>) -> Vec<U> effects E {
    xs.into_iter().map(f).collect()
    // map 的效果 = f 的效果（效果多态传播）
}

// 效果消除
fn block_on<T>(f: impl Future<Output = T>) -> T effects {} {
    // 将 Async 效果消除，同步返回结果
}
```

### 4.2 与 Trait 系统的整合挑战

```text
挑战 1: Trait bound 与效果约束的交互
  trait Reader {
      fn read(&mut self, buf: &mut [u8]) -> Result<usize, Error>;
      // 如果 read 需要 Io effect，trait 定义是否需要标注？
  }

挑战 2: 效果子类型
  fn foo() -> i32 effects {Io}  <:  fn foo() -> i32 effects {Io, Async}
  // 效果更少 = 更"纯" = 子类型？（与常规子类型方向相反）

挑战 3: 向后兼容
  现有 async/unsafe/const 关键字如何迁移到统一效果系统？
  → 最可能路径: 保留关键字，内部 desugar 为效果标记
```

### 4.2 效果传播时序图

```mermaid
sequenceDiagram
    autonumber
    participant Caller as 调用者 foo()
    participant Callee as 被调用者 bar()
    participant EffectSys as 效果系统
    participant Runtime as 运行时/处理器

    Caller->>Callee: 调用 async fn bar()
    activate Callee
    Callee-->>Caller: 返回 impl Future<br/>(携带 Async 效果)
    deactivate Callee

    Caller->>EffectSys: 效果污染检查<br/>foo 是否允许 Async 效果?
    EffectSys-->>Caller: 效果传播确认<br/>foo 也必须 async 或 block_on

    alt 异步处理
        Caller->>Runtime: .await / spawn(task)
        Runtime->>Callee: poll Future
        Callee-->>Runtime: Poll::Ready / Pending
        Runtime-->>Caller: Future 完成<br/>(Async 效果消除)
    else 同步阻塞
        Caller->>Runtime: block_on(future)
        Runtime->>Runtime: 忙等待/线程阻塞
        Runtime-->>Caller: 同步返回 T<br/>(Async 效果 → 无效果)
    end

    note over Caller,Runtime: 效果多态场景<br/>AsyncFn 允许 F: sync 或 async<br/>效果变量 e 在调用点实例化
```

> **认知功能**: 此序列图将"效果污染"和"效果消除"的动态过程可视化。**步骤 1-2** 展示效果产生（被调用者返回携带效果的值），**步骤 3-4** 展示效果传播（效果系统强制调用者承担相同效果），**步骤 5-9** 展示效果处理（运行时通过 poll/await 消除效果）。关键洞察：**效果多态（AsyncFn）允许调用者在不知道被调用者具体效果的情况下编写泛型代码——效果变量 `e` 在调用点被实例化**。

### 4.3 `gen` blocks 与效果叠加

> **[来源: rust-lang/rust #117078]**

`gen` blocks（生成器）是 Rust 正在探索的另一个效果：

```rust,ignore
// gen block: 效果 = 可挂起并产生多个值
let iter = gen {
    yield 1;
    yield 2;
    yield 3;
};
```

`gen` 与 `async` 的对偶关系：

| 维度 | `async {}` | `gen {}` |
|:---|:---|:---|
| 效果 | 异步挂起 | 同步产生 |
| 返回 | 单个 `Future` | 多个 `Iterator` 元素 |
| 挂起点 | `.await` | `yield` |
| 状态机 | Future 状态机 | Generator 状态机 |
| 形式化 | Continuation monad | 余代数（coalgebra） |

> **理论洞察**: `async` 和 `gen` 都是**计算效果**的具体实例。在完整的代数效应框架中，它们可以由统一的效果声明派生：`async = effect Suspend with Resume; gen = effect Yield with Next`。

---

## 五、演进路线图与开放问题

### 5.1 语言团队已知讨论（公开信息）

| 时间 | 事件 | 状态 |
|:---|:---|:---|
| 2023 | Lang Team Blog: "Effects in Rust" 概念文章 | 概念探索 |
| 2024 | `AsyncFn` trait 稳定（1.85） | ✅ 效果多态原型落地 |
| 2024 | `gen` blocks 进入 nightly | 🚧 新效果类型实验 |
| 2025 | Effects 语法讨论在 internals.rust-lang.org | 🚧 社区辩论中 |
| 202? | 统一 `effect` 关键字 | 🔮 远期可能 |

### 5.2 开放问题（Research Questions）

```text
Q1: Rust 需要完整的代数效应，还是类型效应就足够了？
    → 观点 A: 类型效应足够，保持零成本和简单性
    → 观点 B: 代数效应的 handler 机制能统一 async/iterator/exception

Q2: 效果系统如何与 Unsafe 交互？
    → unsafe 是一种"能力（capability）"而非"效果"
    → 但 unsafe fn 确实改变了调用上下文的要求

Q3: 效果多态的编译期代价？
    → 效果约束增加类型推断复杂度
    → 需要评估对编译时间的实际影响

Q4: 与现有生态的兼容性？
    → async_trait crate 的 workaround 是否会被原生替代？
    → `futures::Stream` 与 `gen` blocks 的语义对齐
```

### 5.3 概念预研 → 工业落地的条件

```text
必要条件:
  ✅ AsyncFn 证明效果多态在 trait 系统中可行
  ✅ gen blocks 证明多种效果可以共存
  🚧 需要统一的语法设计（不破坏现有代码）
  🚧 需要编译器实现团队承诺支持
  🚧 需要 Edition 迁移策略（可能 2027+）
```

---

## 六、相关概念链接

| 概念 | 文件 | 关系 |
|:---|:---|:---|
| Async/Await | [`../03_advanced/02_async.md`](../03_advanced/02_async.md) | `Async` 效果的主要载体 |

---

## 七、定理一致性矩阵（效果系统类型安全）

> **[来源类型: 原创分析; Koka; Plotkin & Pretnar 2009]** 以下矩阵梳理效果系统的类型安全保证与 Rust 的渐进式实现。

| 编号 | 效果 / 保证 | 前提 | 结论 | 失效条件 | 后果 |
|:---|:---|:---|:---|:---|:---|
| **EF1** | `async` 效果追踪 | `async fn` 关键字 | 调用者必须 `await` 或 `spawn` | 阻塞调用在 async 上下文 | 执行器线程阻塞 |
| **EF2** | `unsafe` 效果边界 | `unsafe fn` / `unsafe {}` | 调用者承担 safety proof 义务 | 调用者未验证 precondition | UB（未定义行为） |
| **EF3** | `const` 效果限制 | `const fn` 关键字 | 仅编译期可求值操作 | 运行时依赖；堆分配 | 编译错误 |
| **EF4** | `AsyncFn` 效果多态 | `AsyncFn` trait bound | 泛型代码接受 sync/async 闭包 | trait 系统表达能力不足 | 无法抽象异步回调 |
| **EF5** | 统一 `effect` 关键字（未来） | 语法设计完成 + Edition 迁移 | 所有副作用显式追踪 | 向后兼容破坏；推断失败 | 生态迁移成本 |

> **⟹ 推理链**: EF1-EF3 证明 Rust **已经实现了效果的隐性追踪**，只是通过不同关键字而非统一语法。EF4 是**效果多态的原型**——证明统一语法在 trait 系统内可行。EF5 是**远期方向**，其最大障碍不是技术可行性，而是**向后兼容性**和**社区共识**。
| `AsyncFn` Trait | [`../03_advanced/02_async.md`](../03_advanced/02_async.md) §12 | 效果多态的工程原型 |
| `gen` blocks | [`../03_advanced/02_async.md`](../03_advanced/02_async.md) §13 | 另一种计算效果的实验 |
| 类型论基础 | [`../04_formal/02_type_theory.md`](../04_formal/02_type_theory.md) | 效果系统的类型论根基 |
| Rust 版本跟踪 | [`./05_rust_version_tracking.md`](./05_rust_version_tracking.md) | 效果相关语言特性状态 |
| 语言演进 | [`./03_evolution.md`](./03_evolution.md) §2.1, §2.3.1 | 效果系统在长程演进中的定位 |

> **[来源: Plotkin & Pretnar 2009 — Algebraic Effects; Koka Documentation; Eff Language]** Effect 系统概念基于代数效应的经典论文和现代语言实现。✅

> **[来源: Rust Lang Team Blog; Rust Internals Discussion; RFC 3668 AsyncFn]** Rust 效果追踪分析基于语言团队的公开讨论和稳定化的 trait 系统。✅

> **[来源: Haskell GHC; Java Checked Exceptions; Type Theory Research]** 跨语言对比参考了多种语言的效果处理机制和类型论研究。✅
---

---

## Wikipedia 概念对齐

> **[来源: Wikipedia]** 核心概念与国际知识库映射。

| 概念 | Wikipedia 词条 | 说明 |
|:---|:---|:---|
| **Effect system** | [Effect system](https://en.wikipedia.org/wiki/Effect_system) | 效果系统 |
| **Monad (functional programming)** | [Monad (functional programming)](https://en.wikipedia.org/wiki/Monad_(functional_programming)) | Monad |
| **Algebraic effect** | [Algebraic effect](https://en.wikipedia.org/wiki/Algebraic_effect) | 代数效果 |

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **权威来源对齐变更日志**: 2026-05-19 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新: 2026-05-21
**状态**: ✅ 权威来源对齐完成 (Batch 8)
