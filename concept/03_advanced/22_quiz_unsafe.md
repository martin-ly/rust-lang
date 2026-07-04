> **内容分级**: [专家级]

# 测验：Unsafe Rust（L3 试点扩展）
>
> **EN**: Unsafe Rust
> **Summary**: Quiz Unsafe. Core Rust concept.
> **受众**: [专家]
> **内容分级**: [专家级]
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链
> **后置概念**: N/A
---

> **来源**: · [Unsafe Rust](03_unsafe.md) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [The Rust Programming Language — Ch19 Unsafe Rust](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) ·
> [Rustonomicon](https://doc.rust-lang.org/nomicon/) ·
> [Rust Reference — Unsafe Operations](https://doc.rust-lang.org/reference/unsafe-blocks.html)
>
> **前置概念**: [Error Handling](../02_intermediate/04_error_handling.md)
> [Unsafe Rust](03_unsafe.md) ·
> [Ownership](../01_foundation/01_ownership.md) ·
> [Borrowing](../01_foundation/02_borrowing.md)
>
> **对应练习**:
> [`exercises/src/unsafe_rust/`](../../exercises/src/unsafe_rust)

---

> **Bloom 层级**: 分析 → 评价
> **定位**: L3 嵌入式互动测验——验证 Unsafe Rust 核心概念（原始指针（Raw Pointer）、unsafe 块/函数/Trait、 FFI、 Miri 验证）的掌握程度。
> **⚠️ 警告**: 本测验涉及 `unsafe` 代码。请在充分理解安全 Rust 后再尝试，且所有 `unsafe` 操作需经过 Miri 验证。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---


---

## 认知路径

> **认知路径**: 本节从 "测验" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 测验 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 测验 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与测验的适用边界。
5. **迁移应用**: 将 测验 与前置/后置概念链接，形成跨层知识网络。


---

> **过渡**: 从 测验 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 测验 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 测验 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。


---

> **定理 1** [Tier 2]: 测验 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 测验 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 测验 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。


---

## 反命题决策树

> **反命题 1**: "测验 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 测验 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 测验 规则被违反的直接信号。

> **反命题 3**: "其他语言对 测验 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 测验 具有语言特有的形态。


---

> **反向推理 1**: 如果程序在 测验 相关代码处出现编译错误 ⟸ 应首先检查所有权（Ownership）、生命周期（Lifetimes）或类型约束是否被违反。
>
> **反向推理 2**: 如果某段代码在运行时（Runtime）表现出非预期行为且与 测验 有关 ⟸ 应回溯到其形式化语义或安全边界假设，定位隐式契约。


## 一、Unsafe 基础语义

### Q1. 以下代码能否编译？`unsafe` 关键字的作用是什么？

```rust
fn main() {
    let mut num = 5;
    let r1 = &num as *const i32;
    let r2 = &mut num as *mut i32;
    unsafe {
        println!("r1 is: {}", *r1);
        println!("r2 is: {}", *r2);
    }
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，但 **Miri 会报告 Undefined Behavior**。

**输出**：

```
r1 is: 5
r2 is: 5
```

**解析**：代码创建了一个不可变原始指针（Raw Pointer） `r1` 和一个可变原始指针 `r2`，同时指向同一数据。虽然这在 `unsafe` 块中允许，但违反了 Rust 的**别名规则**（Aliasing XOR Mutation）。

**Miri 检测**：

```bash
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri run
# 错误：SharedReadOnly pointer used after mutable borrow
```

**`unsafe` 的五大操作**：

1. 解引用（Reference）原始指针（Raw Pointer）
2. 调用 `unsafe` 函数或方法
3. 访问或修改可变的静态变量
4. 实现 `unsafe` trait
5. 访问 `union` 的字段

**关键原则**：`unsafe` 不关闭借用（Borrowing）检查器——它允许你执行编译器无法验证的操作，但**你**必须保证安全性。

**知识点**：`unsafe` 是"信任程序员"的契约，不是"关闭检查器"。每个 `unsafe` 块都应附带安全不变量的注释。[→ Unsafe 详解](03_unsafe.md)

</details>

---

### Q2. 以下代码能否编译？解释 `unsafe fn` 与 `unsafe` 块的职责分离

```rust,compile_fail
unsafe fn dangerous() {
    println!("This is unsafe");
}

fn main() {
    dangerous();
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`call to unsafe function requires unsafe function or block`

**解析**：调用 `unsafe fn` 必须在 `unsafe` 块或另一个 `unsafe fn` 中。

**修正**：

```rust
unsafe fn dangerous() {
    println!("This is unsafe");
}

fn main() {
    unsafe {
        dangerous();
    }
}
```

**职责分离**：

| 元素 | 含义 | 调用者责任 |
|:---|:---|:---|
| `unsafe fn` | 函数内部有编译器无法验证的操作 | 确保满足函数的前提条件 |
| `unsafe { ... }` | 块内有编译器无法验证的操作 | 确保块内的所有操作安全 |
| `unsafe trait` | Trait 的实现有不安全约束 | 确保实现满足 Trait 的安全契约 |

**最佳实践**：`unsafe fn` 的文档必须明确说明**调用者必须保证的不变量**。

**知识点**：`unsafe fn` 将安全责任**转移给调用者**。调用方必须在 `unsafe` 块中显式承担这一责任。[→ Unsafe 详解](03_unsafe.md)

</details>

---

## 二、原始指针与内存安全

### Q3. 以下代码能否编译？存在什么风险？

```rust
fn main() {
    let ptr = 0x12345 as *const i32;
    unsafe {
        println!("{}", *ptr);
    }
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，但**运行期可能 segfault**。

**解析**：`0x12345 as *const i32` 创建了一个**悬垂/无效原始指针（Raw Pointer）**。解引用（Reference）它是未定义行为（UB）。

**原始指针（Raw Pointer） vs 引用（Reference）**：

| 特性 | 原始指针（Raw Pointer） `*const T` / `*mut T` | 引用（Reference） `&T` / `&mut T` |
|:---|:---|:---|
| 可为 null | ✅ | ❌ |
| 可悬垂 | ✅ | ❌（编译期保证） |
| 可别名 | ✅（多个 `*mut` 同时存在） | ❌ |
| 自动解引用（Reference） | ❌ | ✅ |
| 生命周期（Lifetimes）检查 | ❌ | ✅ |

**安全创建原始指针（Raw Pointer）的方式**：

```rust
let num = 5;
let r1 = &num as *const i32;  // 从有效引用创建
```

**知识点**：原始指针的主要用途是与 C 代码交互（FFI）和构建安全抽象（如 `Vec`、`Box` 的内部实现）。[→ Unsafe 详解](03_unsafe.md)

</details>

---

### Q4. 以下代码能否编译？Miri 会如何报告？

```rust
fn main() {
    let mut v = vec![1, 2, 3, 4, 5];
    let ptr = v.as_mut_ptr();
    let len = v.len();

    unsafe {
        v.set_len(0); // 清空 Vec 而不释放内存
    }

    let slice = unsafe { std::slice::from_raw_parts(ptr, len) };
    println!("{:?}", slice);
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，但 **Miri 会报告 Undefined Behavior**。

**解析**：`v.set_len(0)` 后，`Vec` 认为自己没有元素，但底层内存仍然有效。然而，`ptr` 是从 `v` 借用（Borrowing）的，当 `v` 重新获得所有权（Ownership）时（函数结束），`ptr` 的使用可能与 `v` 的 drop 冲突。

**更深层问题**：即使 Miri 不报错，这种代码也是极度危险的。正确做法：

```rust
fn main() {
    let mut v = vec![1, 2, 3, 4, 5];
    let ptr = v.as_mut_ptr();
    let len = v.len();
    let cap = v.capacity();

    std::mem::forget(v); // 防止 v drop 内存

    let slice = unsafe { std::slice::from_raw_parts(ptr, len) };
    println!("{:?}", slice);

    // 必须手动释放内存！
    unsafe {
        let _ = Vec::from_raw_parts(ptr, len, cap);
    } // _ 在此处 drop，释放内存
}
```

**知识点**：`Vec::from_raw_parts` 和 `mem::forget` 是构建自定义集合的核心工具，但也是 UB 高发区。每次使用都必须确保内存生命周期（Lifetimes）正确。→ Unsafe 模式详解

</details>

---

## 三、Unsafe Trait 与 FFI

### Q5. 以下代码能否编译？解释 `Sync` 和 `Send` 的 `unsafe impl`

```rust
use std::cell::Cell;

struct MyType {
    data: Cell<i32>,
}

unsafe impl Send for MyType {}
unsafe impl Sync for MyType {}

fn main() {
    let data = MyType { data: Cell::new(0) };
    std::thread::spawn(move || {
        data.data.set(1);
    }).join().unwrap();
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，但**存在数据竞争**。

**解析**：`Cell<T>` 提供**内部可变性**，但不是线程安全的。`unsafe impl Send` 和 `unsafe impl Sync` 是程序员向编译器保证"这个类型可以安全地跨线程移动/共享"——但这个保证在这里是**错误的**。

**为什么 `Cell` 不是 `Sync`**：

`Cell::set` 在修改值时不进行任何同步（无锁、无原子操作（Atomic Operations））。如果两个线程同时通过 `&Cell` 调用 `set`，会导致数据竞争。

**正确方案**：使用 `Mutex<Cell<i32>>` 或 `AtomicI32`：

```rust
use std::sync::atomic::{AtomicI32, Ordering};

struct MyType {
    data: AtomicI32,
}

// AtomicI32 自动实现 Send + Sync，无需 unsafe impl
```

**关键原则**：`unsafe impl Send/Sync` 是最危险的 `unsafe` 操作之一——它允许编译器相信一个类型的线程安全性，若保证错误则会导致整个程序的并发安全（Concurrency Safety）崩溃。

**知识点**：永远不要为包含非线程安全内部可变性的类型 `unsafe impl Sync`。[→ 并发模型详解](01_concurrency.md)

</details>

---

### Q6. 以下代码存在什么问题？这是 FFI 的经典陷阱

```rust,ignore
extern "C" {
    fn abs(input: i32) -> i32;
}

fn main() {
    unsafe {
        println!("Absolute value of -3: {}", abs(-3));
    }
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译并运行（输出 `3`），但存在**未定义行为风险**。

**解析**：`extern "C"` 块声明了 C 函数的接口，但 Rust 编译器**完全信任**这个声明。如果声明与实际 C 函数不匹配，UB 发生。

**潜在问题**：

1. **函数签名不匹配**：如果 C 的 `abs` 实际接受 `long`（64 位），但声明为 `i32`（32 位），参数传递错误
2. **函数不存在**：链接时或运行时（Runtime）可能找不到符号
3. **调用约定错误**：`extern "C"` 使用 C 调用约定，但如果实际函数使用 `stdcall` 或其他约定，栈会损坏

**更安全的做法**——使用 `libc` crate：

```rust,ignore
use libc::abs;

fn main() {
    unsafe {
        println!("{}", abs(-3));
    }
}
```

**Rust 1.82+ 改进**：`unsafe extern "C" fn` 和 `safe` 关键字允许更细粒度的 FFI 安全边界控制。

**知识点**：FFI 是 Rust 与外部世界交互的边界，也是 UB 的主要来源。精确的签名声明和边界测试是必须的。[→ FFI 详解](05_rust_ffi.md)

</details>

---

## 四、综合应用

### Q7. 以下代码能否编译？`MaybeUninit` 的作用是什么？

```rust
use std::mem::MaybeUninit;

fn main() {
    let mut x = MaybeUninit::<i32>::uninit();
    unsafe {
        x.as_mut_ptr().write(42);
        println!("{}", x.assume_init());
    }
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出 `42`。

**解析**：`MaybeUninit<T>` 是 Rust 中处理**未初始化内存**的标准类型。

**背景问题**：

```rust,compile_fail
let x: i32; // 未初始化
println!("{}", x); // 编译错误！
```

`MaybeUninit` 允许你：

1. 分配 `T` 大小的内存但不初始化
2. 通过原始指针手动写入值
3. 在确认初始化后，通过 `assume_init()` 转换为 `T`

**危险操作**：

```rust,ignore
let x = MaybeUninit::<i32>::uninit();
unsafe {
    println!("{}", x.assume_init()); // UB！未初始化就读取
}
```

**使用场景**：

- 与 C 结构体（Struct）交互（C 允许部分初始化）
- 实现 `Vec::with_capacity`（分配内存但延迟初始化）
- 构建自定义集合类型

**知识点**：`MaybeUninit` 是 Rust 1.36+ 替代 `std::mem::uninitialized` 的安全工具。后者已废弃，因为可能实例化无效值。[→ Unsafe 详解](03_unsafe.md)

</details>

---

### Q8. 以下代码的输出是什么？解释 `std::ptr::read` 和 `std::ptr::write`

```rust
fn main() {
    let mut x = Box::new(42);
    let ptr = &mut *x as *mut i32;

    unsafe {
        let val = std::ptr::read(ptr);
        println!("Read: {val}");
        std::ptr::write(ptr, val + 1);
        println!("After write: {}", *x);
    }
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

```
Read: 42
After write: 43
```

**解析**：

- `std::ptr::read(ptr)`：从 `ptr` 指向的地址**按位复制**值（不获取所有权（Ownership））
- `std::ptr::write(ptr, val)`：将值**按位写入** `ptr` 指向的地址（不 drop 旧值）

**危险对比**：

```rust
// ❌ 危险：read 后 Box 仍认为自己拥有值，导致双重释放
let b = Box::new(42);
let ptr = Box::into_raw(b);
unsafe {
    let _val = std::ptr::read(ptr); // 复制值
} // b 被 drop，ptr 指向的内存也被释放！
// 若再次使用 ptr → use-after-free
```

**正确做法**：

```rust,ignore
let b = Box::new(42);
let ptr = Box::into_raw(b); // 转移所有权到原始指针
unsafe {
    let val = std::ptr::read(ptr);
    std::ptr::drop_in_place(ptr); // 显式 drop
    std::alloc::dealloc(ptr as *mut u8, layout); // 显式释放
}
```

**知识点**：`ptr::read` / `ptr::write` 是 Rust 标准库内部实现的核心原语，也是手动内存管理的起点。[→ Unsafe 模式详解](12_unsafe_rust_patterns.md)

</details>

---

### Q9. 以下代码存在什么问题？解释 `unsafe_op_in_unsafe_fn`

```rust
unsafe fn raw_add(a: *const i32, b: *const i32) -> i32 {
    *a + *b
}

fn main() {
    let x = 1;
    let y = 2;
    unsafe {
        println!("{}", raw_add(&x, &y));
    }
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：在 Rust 2021 Edition 下 ❌ 不能编译；在 2024 Edition 下默认 ✅ 能编译（但行为不同）。

**解析**：Rust 2024 Edition 引入了 `unsafe_op_in_unsafe_fn` lint 默认开启：

- **2021 及之前**：`unsafe fn` 内部自动视为 `unsafe` 上下文，无需额外 `unsafe` 块
- **2024 Edition**：`unsafe fn` 内部的操作仍需显式 `unsafe` 块，清晰标识**哪些具体操作**是不安全的

**2024 Edition 修正**：

```rust
unsafe fn raw_add(a: *const i32, b: *const i32) -> i32 {
    unsafe { *a + *b } // 显式标记解引用是不安全的
}
```

**设计哲学**：

- `unsafe fn` = "调用此函数需要满足前提条件"
- `unsafe {}` = "此块内有编译器无法验证的操作"

分离两者使代码更清晰——读者可以一眼看出函数体内**具体哪些操作**需要额外关注。

**知识点**：Rust 2024 Edition 的 `unsafe_op_in_unsafe_fn` 是 Unsafe Rust 可用性的重要改进，已在项目中通过 `.cargo/config.toml` 的 `edition = "2024"` 启用。[→ Unsafe 详解](03_unsafe.md)

</details>

---

### Q10. 以下代码能否编译？Miri 会报告什么问题？

```rust
fn main() {
    let mut data = [0u8; 4];
    let ptr = data.as_mut_ptr();

    unsafe {
        let int_ptr = ptr as *mut u32;
        *int_ptr = 0x12345678;
    }

    println!("{:?}", data);
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，但 **Miri 会报告 Undefined Behavior**（在严格架构下）。

**解析**：`ptr as *mut u32` 将 `u8` 指针转换为 `u32` 指针，然后写入。这涉及**类型双关（type punning）**。

**Miri 错误**（Stacked Borrows / Tree Borrows）：

```
error: Undefined Behavior: trying to retag from <tag> for Unique permission
```

**问题**：`u8` 数组和 `u32` 指针的别名规则不兼容。`u32` 写入需要一个指向整个 4 字节区域的独占引用（Reference），但原始 `data` 数组的借用（Borrowing）仍然存在。

**正确做法**——使用 `std::ptr::write_unaligned` 或 `std::slice::align_to`：

```rust
fn main() {
    let mut data = [0u8; 4];
    unsafe {
        std::ptr::write_unaligned(data.as_mut_ptr() as *mut u32, 0x12345678);
    }
    println!("{:?}", data);
}
```

**注意**：即使使用 `write_unaligned`，若 `data` 的地址不是 4 字节对齐的，某些架构（如 ARM）可能产生硬件异常。x86/x86_64 支持非对齐访问，但性能较低。

**知识点**：原始指针的类型转换不等于合法访问。Rust 的别名模型（Stacked Borrows / Tree Borrows）对指针的类型和权限有严格要求。[→ Unsafe 详解](03_unsafe.md)

</details>

---

## 五、评分参考

| 得分 | 评价 | 建议 |
|:---:|:---|:---|
| 10/10 | 🏆 Unsafe 边界已内化 | 进阶至 [Unsafe Patterns](12_unsafe_rust_patterns.md) 或尝试为 crates/ 编写 unsafe 抽象 |
| 7–9/10 | ✅ 核心概念掌握 | 强化 [Unsafe 练习](../../exercises/src/unsafe_rust)，用 Miri 验证所有代码 |
| 4–6/10 | 🔄 需巩固基础 | 重读 [Unsafe Rust](03_unsafe.md) · [Rustonomicon](https://doc.rust-lang.org/nomicon/) |
| 0–3/10 | 📚 建议重新开始 | 从 [Ownership](../01_foundation/01_ownership.md) 确认基础，再读 Unsafe 章节 |

---

> **对应练习**: [`exercises/src/unsafe_rust/`](../../exercises/src/unsafe_rust)

---

> **权威来源**: [The Rust Programming Language — Ch19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) · [Rustonomicon](https://doc.rust-lang.org/nomicon/) · [Rust Reference — Unsafe Rust](https://doc.rust-lang.org/reference/unsafe-blocks.html)

## 嵌入式测验（Embedded Quiz）

### 测验 1：本文件是 测验：Unsafe Rust（L3 试点扩展） 的专项测验集。这类测验文件的主要作用是什么？（理解层）

**题目**: 本文件是 测验：Unsafe Rust（L3 试点扩展） 的专项测验集。这类测验文件的主要作用是什么？

<details>
<summary>✅ 答案与解析</summary>

集中提供大量针对特定主题的练习题，帮助学习者系统检验和巩固对该主题的掌握程度，补充概念文件中的嵌入式测验。
</details>

---

### 测验 2：在 测验：Unsafe Rust（L3 试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？（理解层）

**题目**: 在 测验：Unsafe Rust（L3 试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？

<details>
<summary>✅ 答案与解析</summary>

先尝试独立作答，然后对照答案解析理解错误原因，最后回到对应的概念文件重新阅读相关章节，形成"测验-反馈-复习"的闭环。
</details>

---

### 测验 3：专项测验与概念文件末尾的嵌入式测验有什么区别？（理解层）

**题目**: 专项测验与概念文件末尾的嵌入式测验有什么区别？

<details>
<summary>✅ 答案与解析</summary>

专项测验题量更大、覆盖更全面，通常按难度分层；嵌入式测验更精简，直接关联刚阅读的概念内容，用于即时检验理解。
</details>
