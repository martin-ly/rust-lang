> **内容分级**: [专家级]

# Cross-Platform Concurrency（跨平台并发）
>
> **EN**: Cross-Platform Concurrency
> **Summary**: Platform-specific threading models, synchronization primitives, and conditional-compilation strategies for writing portable concurrent Rust across Windows, Linux, macOS, and mobile targets.
> **受众**: [专家]
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: C×Eva — 评价并发设计在不同平台下的可移植性
> **前置依赖**: [Concurrency](01_concurrency.md) · [Conditional Compilation](../03_proc_macros/28_conditional_compilation.md)
> **后置概念**: [Rust for Linux](../../07_future/04_research_and_experimental/43_rust_for_linux.md)
>
> **主要来源**: [Rust Reference — Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html) · [std::thread](https://doc.rust-lang.org/std/thread/) · [Rust Platform Support](https://doc.rust-lang.org/nightly/rustc/platform-support.html)

---

## 一、平台线程模型概览

| 平台 | 线程模型 | 关键原生 API |
|:---|:---|:---|
| Windows | 1:1（用户线程 : 内核线程），纤程（Fibers），线程池 API | `CreateThread`, SRWLock, IOCP |
| Linux | NPTL 1:1，轻量级进程（LWP） | `pthread`, `futex`, `epoll`/`io_uring` |
| macOS | POSIX 线程 + Grand Central Dispatch | `pthread`, GCD, `NSOperationQueue` |
| Android / iOS | 继承 Linux / Darwin 模型，附加后台执行限制 | JNI, QoS |

Rust 的 `std::thread` 与 `std::sync` 已封装大部分差异，但跨平台优化仍需理解底层实现。

---

## 二、同步原语的平台实现

```rust
use std::sync::Mutex;

fn mutex_example() {
    let m = Mutex::new(0);
    // Windows: SRWLock (Slim Reader/Writer Lock)
    // Linux / macOS: pthread_mutex
    *m.lock().unwrap() += 1;
}
```

平台特定代码应使用 `#[cfg(target_os = "...")]` 隔离，并对外暴露统一接口。

---

## 三、条件编译与平台抽象

```rust
#[cfg(target_os = "windows")]
fn optimal_thread_count() -> usize {
    std::env::var("NUMBER_OF_PROCESSORS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(4)
}

#[cfg(not(target_os = "windows"))]
fn optimal_thread_count() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
}
```

**最佳实践**:

1. 优先使用 Rust 标准库抽象。
2. 用 `#[cfg]` 清晰隔离平台特定代码，并提供默认实现。
3. 在 CI 中覆盖所有目标平台。
4. 文档化平台差异与性能特性。

---

## 四、移动平台注意事项

- **Android**: 后台线程常通过 JNI 暴露；注意 `setpriority` 与电量管理限制。
- **iOS**: 后台执行受严格限制，应使用 QoS / GCD 而非长时间运行的原生线程。

---

## 权威来源索引

- [Rust Reference — Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html)
- [Rust Platform Support](https://doc.rust-lang.org/nightly/rustc/platform-support.html)
- [std::thread](https://doc.rust-lang.org/std/thread/)
