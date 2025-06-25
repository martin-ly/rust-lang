# `c06_async` 模块术语表

### `async`/`await`
- **定义**: Rust 用于编写异步代码的语法关键字。`async` 用于定义一个异步函数或代码块，它返回一个 `Future`。`await` 用于暂停一个 `async` 函数的执行，直到其等待的 `Future` 完成。
- **关联章节**: `01_introduction_and_philosophy.md`

### `Future`
- **定义**: 一个 Trait，代表一个可以随时间推移而产生的值。这是 Rust 异步计算的核心抽象。`Future` 通过 `poll` 方法被驱动，直到产生一个最终值。
- **关联章节**: `01_introduction_and_philosophy.md`, `03_pinning_and_unsafe_foundations.md`

### 运行时 (Runtime)
- **定义**: 一个库，提供了执行异步代码所需的服务。它包含一个或多个执行器、一个 I/O 事件反应器（如 epoll, kqueue）、定时器以及任务调度逻辑。`tokio` 和 `async-std` 是最流行的运行时。
- **关联章节**: `02_runtime_and_execution_model.md`

### 执行器 (Executor)
- **定义**: 运行时的核心组件，负责接收异步任务（`Future`），并通过重复调用 `poll` 方法来驱动它们直至完成。
- **关联章节**: `02_runtime_and_execution_model.md`

### `Pin<T>`
- **定义**: 一个智能指针，用于"固定"一个对象在内存中的位置，防止其被移动。这对于安全地处理自引用结构至关重要，而自引用结构是 `async`/`await` 状态机的常见实现方式。
- **关联章节**: `03_pinning_and_unsafe_foundations.md`

### `Unpin`
- **定义**: 一个自动 Trait，用于标记那些即使被 `Pin` 包裹也可以安全移动的类型。绝大多数 Rust 类型都是 `Unpin` 的。如果一个类型不是 `Unpin`，它通常是自引用的。
- **关联章节**: `03_pinning_and_unsafe_foundations.md`

### `Stream`
- **定义**: 一个 Trait，代表一个异步的值序列。它是 `Iterator` 的异步等价物。
- **关联章节**: `04_streams_and_sinks.md`

### `Sink`
- **定义**: 一个 Trait，代表一个可以异步接收值的地方。它是 `Stream` 的对偶概念，用于异步写入数据。
- **关联章节**: `04_streams_and_sinks.md`

### 函数颜色 (Function Coloring)
- **定义**: 一个描述编程语言中 `async` 和 `sync` 函数之间交互限制的术语。它指出了 `async` 代码倾向于"病毒式"传播，以及 `async`/`sync` 边界处需要谨慎处理的架构问题。
- **关联章节**: `06_critical_analysis_and_advanced_topics.md`

### `Waker`
- **定义**: 一个由执行器提供给 `Future` 的句柄。当一个 `Future` 在 `poll` 时返回 `Poll::Pending`，它必须存储这个 `Waker`。当 `Future` 准备好再次被轮询时（例如，一个 I/O 事件已发生），它会调用 `waker.wake()` 来通知执行器。
- **关联章节**: `01_introduction_and_philosophy.md`, `02_runtime_and_execution_model.md`

### `async-trait`
- **定义**: 一个流行的第三方 crate，它通过宏提供了在 Trait 中使用 `async fn` 的能力。它通过将 `Future` 包装在 `Box<dyn Future>` 中来实现对象安全。
- **关联章节**: `05_async_in_traits_and_ecosystem.md` 