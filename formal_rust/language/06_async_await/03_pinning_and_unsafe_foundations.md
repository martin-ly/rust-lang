# C06-03. Pinning 与 Unsafe 基础

`async/await` 的一个核心挑战在于 `Future` 在 `.await` 点暂停和恢复时，其状态必须在内存中保持稳定。如果一个 `Future` 内部包含了对自身数据的引用（即自引用结构），那么移动这个 `Future` 可能会使这些内部指针失效，导致内存不安全。

Rust 的 `Pin<T>` 类型系统是解决这个问题的关键。本章深入探讨 `Pin` 的工作原理，以及它如何为异步代码提供必要的内存安全保证，即便是在涉及 `unsafe` 的底层实现中。

## 1. 自引用问题 (The Self-Referential Problem)

在同步 Rust 代码中，值可以自由地在栈或堆上移动。所有权系统确保了在任何时刻都只有一个有效的引用或所有者，从而防止了悬垂指针。

然而，异步 `Future` 改变了这一格局。一个 `async` 函数体会被编译器转换成一个实现了 `Future` Trait 的匿名结构体。这个结构体包含了函数的所有局部变量，包括在 `.await` 点之间保持活跃状态的变量。

```rust
async fn example() {
    let mut x = [0; 128];
    let mut read_into_buf = SomeFuture::new(&mut x); // `read_into_buf` 包含对 `x` 的引用

    // 在 `.await` 时，`example` future 可能会被移动
    read_into_buf.await;

    println!("{:?}", &x[0..10]);
}
```

在上面的例子中，`example` 函数对应的 `Future` 结构体同时包含了 `x` 和 `read_into_buf`。`read_into_buf` 又持有对 `x` 的引用。如果这个 `Future` 在内存中的位置被移动（例如，被执行器从一个任务队列移动到另一个），那么 `read_into_buf` 内部的指针就会失效，因为它仍然指向 `x` 的旧地址。

## 2. `Pin<T>`：内存固定

`Pin<T>` 是一个智能指针，它包裹一个其他类型的指针（例如 `Pin<Box<T>>`, `Pin<&mut T>`），并施加一个核心约束：**被 `Pin` 包裹的对象不能被移动**。

- **`Pin<P>`**: `P` 是一个指针类型，如 `Box<T>` 或 `&mut T`。
- **不变性 (Invariant)**: 一旦一个值被 `Pin` 固定，它的内存地址就保证在值的整个生命周期内不会改变，直到它被销毁。

通过 `Pin`，我们可以安全地创建和使用自引用结构。当轮询一个 `Future` 时，执行器会通过 `Pin<&mut dyn Future>` 来调用 `poll` 方法。这个 `Pin` 保证了 `Future` 不会被移动，因此其内部的任何自引用都是安全的。

```rust
use std::pin::Pin;
use std::future::Future;
use std::task::{Context, Poll};

// 一个自引用的 Future
struct MyFuture {
    data: String,
    // 这个指针指向 `data`
    slice: *const u8,
}

impl Future for MyFuture {
    type Output = ();

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
        // 因为 `self` 是 Pin<&mut Self>，我们可以确定它没有被移动。
        // 所以，可以安全地解引用 `slice` 指针。
        println!("Polling... Slice points to: {:?}", self.slice);
        Poll::Ready(())
    }
}
```

## 3. `Unpin` Trait

`Pin` 的约束非常严格。然而，大多数类型并不包含自引用，可以自由移动。为了区分这些类型，Rust 引入了 `Unpin` Trait。

- **`Unpin`**: 一个自动 Trait (auto trait)。如果一个类型的所有字段都是 `Unpin`，那么该类型本身也是 `Unpin`。
- **含义**: 如果 `T: Unpin`，那么即使它被包裹在 `Pin<P<T>>` 中，将它从 `Pin` 中移出也是安全的。基本上，`Unpin` "撤销" 了 `Pin` 的固定效果。

`String`, `u32`, `Vec<T>`, `Box<T>` 等绝大多数标准库类型都是 `Unpin` 的，因为它们不直接存储对自身的引用（堆上数据的地址是稳定的）。

为了在泛型代码中处理 `Pin`，标准库提供了 `Pin::new` 和 `Pin::new_unchecked` 等工具。

- **`Pin::new(value)`**: 只能用于 `Unpin` 的值。因为它本来就可以安全移动，所以创建一个 `Pin` 不会带来风险。
- **`Pin::new_unchecked(value)`**: 一个 `unsafe` 函数。程序员必须向编译器保证，他们会手动维护 `Pin` 的不变性，确保被固定的值在其生命周期内不会被移动。

## 4. `unsafe` 与底层实现

`Pin` 和 `Unpin` 本身并不涉及 `unsafe` 代码。它们是编译时工具，用于强制执行内存安全规则。

然而，**创建**一个真正需要 `Pin` 的自引用结构，或者手动实现 `Future`，通常需要 `unsafe` 代码块。

例如，在 `async` 块的编译器生成代码中，或者在手动实现一个 `Future` 的数据结构时：

1. **构造**: 在构造自引用结构时，可能需要使用 `unsafe` 来创建初始的、可能无效的指针。
2. **固定**: 在首次轮询之前，必须将这个结构 `Pin` 到内存中（例如，通过 `Box::pin`），然后才能安全地初始化内部的自引用指针。
3. **API 边界**: 库作者使用 `unsafe` 和 `Pin` 来提供一个安全的公共 API。例如，`tokio` 的 `spawn` 函数接受任何 `Future`，如果这个 `Future` 不是 `Unpin`，`tokio` 会在内部将其固定在堆上，从而保证它在执行期间不会被移动。

## 总结

- **问题**: `async` `Future` 可能是自引用的，移动它们会破坏内部指针。
- **解决方案**: `Pin<T>` 保证被包裹的值在内存中不会被移动。
- **豁免**: `Unpin` Trait 标记那些可以安全移动的类型，即使它们被 `Pin` 包裹。
- **`unsafe` 的作用**: `Pin` 让我们能够安全地使用自引用结构，但创建这些结构或手动实现底层 `Future` 时，通常需要 `unsafe` 来建立 `Pin` 的安全保证。

`Pin` 是 Rust "无畏并发" 理念在异步世界中的延伸。它是一个复杂的、但绝对必要的工具，用于在零成本抽象的原则下，将 `async/await` 的高级人体工程学与底层的内存安全完美结合。
