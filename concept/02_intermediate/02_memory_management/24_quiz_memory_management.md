> **内容分级**: [综述级]

# 测验：内存管理（L2 试点扩展）
>
> **EN**: Memory Management
> **Summary**: Quiz Memory Management. Core Rust concept.
>
> ```rust fn main() { let b = Box::new(5); println!("{}", b); }```
> <details> <summary>💡 点击展开答案与解析</summary>
> **答案**：✅ 能编译，输出 `5`。 **解析**： | 特性 | 栈分配 | `Box::new`（堆分配） |
> |:---|:---|:---|
> | 存储位置 | 栈 | 堆 |
> | 大小限制 | 栈大小限制（通常 ~8MB） | 仅受可用memory限制 |
> | lifetimes | 作用域结束自动释放 | 离开作用域时 `Box` 被 drop，堆memory释放 |
> | 性能 | 快速（单指令
> **受众**: [进阶]
> **内容分级**: [综述级]
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链
> **后置概念**: N/A
---

> **来源**: · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [Brown Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [The Rust Programming Language — Ch15 Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html) ·
> [Rust Reference — Interior Mutability](https://doc.rust-lang.org/reference/interior-mutability.html)
>
> **前置概念**:
> [Memory Management](03_memory_management.md) ·
> [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) ·
> [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md)
>
> **对应练习**:
> [`exercises/src/ownership_borrowing/ex05_smart_pointer_rc.rs`](../../exercises/src/ownership_borrowing/ex05_smart_pointer_rc.rs)

---

> **Bloom 层级**: 理解 → 应用
> **定位**: L2 嵌入式互动测验——验证智能指针（Smart Pointer）核心概念（Box、Rc/Arc、RefCell/Mutex、内部可变性模式）的掌握程度。
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

## 一、Box 与堆分配

### Q1. 以下代码能否编译？`Box::new` 与栈分配的区别是什么？

```rust
fn main() {
    let b = Box::new(5);
    println!("{}", b);
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出 `5`。

**解析**：

| 特性 | 栈分配 | `Box::new`（堆分配） |
|:---|:---|:---|
| 存储位置 | 栈 | 堆 |
| 大小限制 | 栈大小限制（通常 ~8MB） | 仅受可用内存限制 |
| 生命周期（Lifetimes） | 作用域结束自动释放 | 离开作用域时 `Box` 被 drop，堆内存释放 |
| 性能 | 快速（单指令调整栈指针） | 较慢（需要堆分配器） |

**`Box<T>` 的核心语义**：`Box` 是拥有堆内存所有权（Ownership）的智能指针（Smart Pointer）。`Box` 本身在栈上（只有一个指针大小），但指向的数据在堆上。

**使用场景**：

- 递归类型（如链表、树节点）
- 大对象转移所有权（Ownership）时避免拷贝
- trait 对象（`Box<dyn Trait>`）

**知识点**：`Box` 是最简单的智能指针（Smart Pointer），提供唯一的堆所有权（Ownership），零运行时（Runtime）开销（与 C++ `unique_ptr` 类似）。[→ 内存管理详解](03_memory_management.md)

</details>

---

### Q2. 以下代码能否编译？解释递归类型为什么需要 `Box`

```rust,compile_fail
enum List {
    Cons(i32, List),
    Nil,
}

fn main() {
    let list = List::Cons(1, List::Cons(2, List::Nil));
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`recursive type`List`has infinite size`

**解析**：Rust 需要编译期确定所有类型的大小。`List::Cons(i32, List)` 包含自身，大小无限递归。

**修复方案**——用 `Box` 打破递归：

```rust
enum List {
    Cons(i32, Box<List>),
    Nil,
}

fn main() {
    let list = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
}
```

**为什么 `Box` 能解决这个问题**：

- `Box<List>` 的大小是固定的（一个指针大小）
- 实际数据在堆上，通过指针间接引用（Reference）
- 编译期可以计算 `List` 的大小：`i32` + 指针 = 固定值

**对比其他语言**：

| 语言 | 递归类型表示 |
|:---|:---|
| C | `struct Node { int val; struct Node* next; }` |
| Java | 隐式引用（Reference）（所有对象都在堆上） |
| Rust | 显式 `Box`/`Rc`/`Arc` |

**知识点**：Rust 的"显式堆分配"设计避免了 Java 的全局 GC 和 C 的隐式指针混淆。[→ 内存管理详解](03_memory_management.md)

</details>

---

## 二、Rc 与 Arc

### Q3. 以下代码能否编译？`Rc` 和 `Arc` 的区别是什么？

```rust
use std::rc::Rc;

fn main() {
    let data = Rc::new(vec![1, 2, 3]);
    let data2 = Rc::clone(&data);
    let data3 = data.clone();

    println!("{} {} {}", data.len(), data2.len(), data3.len());
    println!("{}", Rc::strong_count(&data));
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出：

```
3 3 3
3
```

**解析**：

| 特性 | `Rc<T>` | `Arc<T>` |
|:---|:---|:---|
| 名称 | Reference Counted | Atomically Reference Counted |
| 线程安全 | ❌ 单线程 | ✅ 多线程（原子操作（Atomic Operations）） |
| 性能 | 快（非原子加减） | 较慢（原子操作（Atomic Operations）有内存屏障成本） |
| 实现 `Send` | 否 | 是（若 `T: Send + Sync`） |
| 实现 `Sync` | 否 | 是（若 `T: Send + Sync`） |

**引用（Reference）计数规则**：

- `Rc::clone(&data)`：增加强引用（Reference）计数，不克隆数据
- `Rc::strong_count`：当前强引用（Reference）数
- 当 `strong_count` 降为 0，数据被 drop

**常见陷阱**：

```rust,ignore
// ❌ 错误：尝试跨线程使用 Rc
let data = Rc::new(42);
std::thread::spawn(move || {
    println!("{}", *data); // 编译错误！
});
```

**知识点**：`Rc` 是单线程共享所有权（Ownership）的标准工具。任何需要跨线程共享的场景都必须使用 `Arc`。[→ 内存管理详解](03_memory_management.md)

</details>

---

### Q4. 以下代码能否编译？`Rc<RefCell<T>>` 模式的作用是什么？

```rust
use std::cell::RefCell;
use std::rc::Rc;

fn main() {
    let data = Rc::new(RefCell::new(5));

    *data.borrow_mut() += 1;

    let data2 = Rc::clone(&data);
    *data2.borrow_mut() += 1;

    println!("{}", data.borrow());
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出 `7`。

**解析**：`Rc<RefCell<T>>` 是 Rust 中**单线程共享可变状态**的经典模式。

**各组件作用**：

| 类型 | 功能 | 解决的问题 |
|:---|:---|:---|
| `Rc<T>` | 共享所有权（Ownership） | 多个所有者访问同一数据 |
| `RefCell<T>` | 内部可变性 | 通过不可变引用（Immutable Reference）修改数据 |

**内部可变性原理**：`RefCell` 在**运行时（Runtime）**检查借用（Borrowing）规则：

```rust,ignore
data.borrow()     // 获取不可变借用（运行时检查）
data.borrow_mut() // 获取可变借用（运行时检查）
```

**运行时（Runtime） panic 条件**（与编译期借用（Borrowing）检查器相同规则）：

```rust,ignore
let ref_cell = RefCell::new(0);
let b1 = ref_cell.borrow();
let b2 = ref_cell.borrow_mut(); // ❌ 运行时 panic！
```

**对比**：

| 组合 | 线程安全 | 可变性 | 检查时机 |
|:---|:---:|:---|:---:|
| `Rc<RefCell<T>>` | ❌ | ✅ | 运行时（Runtime） |
| `Arc<Mutex<T>>` | ✅ | ✅ | 运行时（Runtime）（锁） |
| `Arc<RwLock<T>>` | ✅ | ✅（读多写少） | 运行时（Runtime）（锁） |

**知识点**：`Rc<RefCell<T>>` 是 Rust 标准库中"绕过编译期借用（Borrowing）检查"的标准方式——不是关闭检查器，而是将检查推迟到运行时（Runtime）。[→ 内存管理详解](03_memory_management.md)

</details>

---

## 三、内部可变性模式

### Q5. 以下代码能否编译？`Cell<T>` 与 `RefCell<T>` 的区别是什么？

```rust
use std::cell::Cell;

fn main() {
    let c = Cell::new(5);
    c.set(10);
    println!("{}", c.get());
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出 `10`。

**解析**：

| 特性 | `Cell<T>` | `RefCell<T>` |
|:---|:---|:---|
| 适用类型 | `Copy` 类型 | 任意类型 |
| 获取内部值 | `.get()`（复制值） | `.borrow()`（返回引用（Reference）） |
| 修改 | `.set(new_val)` | `.borrow_mut()` |
| 运行时（Runtime）检查 | 无（因为值被复制） | 有（借用（Borrowing）规则检查） |
| 开销 | 最低 | 较低（引用（Reference）计数） |

**为什么 `Cell` 不需要运行时（Runtime）借用（Borrowing）检查**：

`Cell::get()` 返回值的**副本**（`T: Copy`），因此不存在多个引用（Reference）同时访问同一数据的问题。

```rust,ignore
let c = Cell::new(5);
let x = c.get(); // x = 5（复制）
c.set(10);       // 修改 Cell 内部
let y = c.get(); // y = 10（复制）
```

**`Cell` 的限制**：

```rust,ignore
let cell = Cell::new(vec![1, 2, 3]);
// ❌ Vec 不实现 Copy，不能用 Cell
```

**选择指南**：

| 场景 | 推荐 |
|:---|:---|
| `T: Copy`，简单值 | `Cell<T>` |
| `T` 任意，需要引用 | `RefCell<T>` |
| 多线程 | `Mutex<T>` / `RwLock<T>` / 原子类型 |

**知识点**：`Cell` 是内部可变性的最低开销实现，但仅限于 `Copy` 类型。理解 `Cell` 与 `RefCell` 的权衡是高效 Rust 代码的关键。[→ 内存管理详解](03_memory_management.md)

</details>

---

### Q6. 以下代码存在什么问题？这是 `Mutex` 使用的经典陷阱

```rust
use std::sync::Mutex;

fn main() {
    let m = Mutex::new(5);
    let mut num = m.lock().unwrap();
    *num = 6;
    println!("{}", *m.lock().unwrap());
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 死锁（或编译错误，取决于具体实现）。

**解析**：`m.lock().unwrap()` 在 `num` 仍然存活时再次调用，导致**同一线程递归加锁**。

**问题分析**：

```rust,ignore
let mut num = m.lock().unwrap(); // 获取锁 #1
*m.lock().unwrap();              // 尝试获取锁 #2 —— 死锁！
```

大多数 `Mutex` 实现（包括 Rust 标准库）是**非递归的**——同一线程不能多次获取同一锁。

**修复方案**——缩小锁的作用域：

```rust
use std::sync::Mutex;

fn main() {
    let m = Mutex::new(5);
    {
        let mut num = m.lock().unwrap();
        *num = 6;
    } // 锁在此处释放
    println!("{}", *m.lock().unwrap()); // ✅ 重新获取锁
}
```

**更优雅的修复**——使用 drop 显式释放：

```rust,ignore
let mut num = m.lock().unwrap();
*num = 6;
drop(num); // 显式释放锁
println!("{}", *m.lock().unwrap());
```

**知识点**：Rust 的 `MutexGuard`（`m.lock()` 的返回值）在离开作用域时自动释放锁。利用这个 RAII 特性管理锁生命周期（Lifetimes）是避免死锁的关键。[→ 并发模式详解](../../03_advanced/10_concurrency_patterns.md)

</details>

---

## 四、Drop 与资源管理

### Q7. 以下代码的输出是什么？解释自定义 `Drop` 的行为

```rust
struct HasDrop {
    name: &'static str,
}

impl Drop for HasDrop {
    fn drop(&mut self) {
        println!("Dropping {}", self.name);
    }
}

fn main() {
    let a = HasDrop { name: "a" };
    {
        let b = HasDrop { name: "b" };
        println!("Inner scope");
    }
    println!("Outer scope");
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

```
Inner scope
Dropping b
Outer scope
Dropping a
```

**解析**：`Drop` trait 在值离开作用域时自动调用，遵循 **LIFO（后进先出）**顺序。

**执行流程**：

1. `a` 创建
2. 进入内部作用域
3. `b` 创建
4. 打印 "Inner scope"
5. 内部作用域结束 → `b` 被 drop → 打印 "Dropping b"
6. 打印 "Outer scope"
7. `main` 结束 → `a` 被 drop → 打印 "Dropping a"

**`Drop` 的使用场景**：

| 场景 | 示例 |
|:---|:---|
| 释放堆内存 | `Box::drop` 释放堆分配 |
| 关闭文件 | `File::drop` 关闭文件描述符 |
| 释放锁 | `MutexGuard::drop` 释放互斥锁 |
| 网络连接清理 | 自定义 TCP 连接的关闭 |

**注意**：不能显式调用 `value.drop()`，必须通过 `drop(value)` 函数或让值离开作用域。

**知识点**：`Drop` 是 Rust RAII（Resource Acquisition Is Initialization）模式的核心。资源释放与生命周期（Lifetimes）绑定，消除了 C 的手动释放和 Java 的 GC 不确定性。→ 内存管理详解

</details>

---

### Q8. 以下代码能否编译？`std::mem::drop` 与 `Drop::drop` 的区别

```rust
struct MyStruct;

impl Drop for MyStruct {
    fn drop(&mut self) {
        println!("Dropped!");
    }
}

fn main() {
    let s = MyStruct;
    std::mem::drop(s);
    // println!("{:?}", s); // 若取消注释会怎样？
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出 `Dropped!`。

**解析**：

| 函数 | 签名 | 作用 |
|:---|:---|:---|
| `std::mem::drop<T>(_x: T)` | 获取所有权（Ownership） | 提前释放值 |
| `Drop::drop(&mut self)` | 可变引用（Mutable Reference） | trait 方法，被编译器自动调用 |

**为什么不能直接调用 `s.drop()`**：

```rust,ignore
s.drop(); // ❌ 编译错误！
```

原因：`drop` 方法在 trait 中被调用时，值可能在部分销毁状态。编译器禁止显式调用以确保安全。

**`std::mem::drop` 的实现**：

```rust
pub fn drop<T>(_x: T) {}
// 获取所有权但不使用，函数结束时值被 drop
```

**取消注释后的结果**：

```rust,ignore
std::mem::drop(s);
println!("{:?}", s); // ❌ 编译错误：use of moved value: s
```

**知识点**：`std::mem::drop` 是提前释放值的标准方式。理解它与 `Drop::drop` 的区别是掌握 Rust 资源管理的关键。[→ 内存管理详解](03_memory_management.md)

</details>

---

## 五、综合应用

### Q9. 以下代码能否编译？这是 `Weak` 指针的经典用例

```rust
use std::rc::{Rc, Weak};
use std::cell::RefCell;

#[derive(Debug)]
struct Node {
    value: i32,
    children: RefCell<Vec<Rc<Node>>>,
    parent: RefCell<Weak<Node>>,
}

fn main() {
    let leaf = Rc::new(Node {
        value: 3,
        children: RefCell::new(vec![]),
        parent: RefCell::new(Weak::new()),
    });

    println!("leaf strong = {}, weak = {}",
        Rc::strong_count(&leaf),
        Rc::weak_count(&leaf));
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出：

```
leaf strong = 1, weak = 0
```

**解析**：`Weak<T>` 是**弱引用**，不增加强引用计数。

**为什么需要 `Weak`**：

假设父子节点都用 `Rc` 互相引用：

```rust,ignore
// 反模式：循环引用导致内存泄漏！
struct BadNode {
    value: i32,
    parent: Option<Rc<BadNode>>,    // 强引用
    children: Vec<Rc<BadNode>>,     // 强引用
}
```

形成 `parent <-> child` 的循环强引用，引用计数永远不会降为 0，内存泄漏。

**`Weak` 解决循环引用**：

| 关系 | 引用类型 | 原因 |
|:---|:---|:---|
| 父 → 子 | `Rc<Node>` | 拥有子节点 |
| 子 → 父 | `Weak<Node>` | 不拥有父节点，避免循环 |

**`Weak` 的操作**：

```rust,ignore
let weak = Rc::downgrade(&rc);    // Rc → Weak
let maybe_rc = weak.upgrade();    // Weak → Option<Rc>
// 若原 Rc 已被 drop，upgrade() 返回 None
```

**知识点**：`Weak` 是 Rust 中处理图结构、树结构中循环引用的标准工具。与垃圾回收语言不同，Rust 要求显式管理这些关系。[→ 内存管理详解](03_memory_management.md)

</details>

---

### Q10. 以下代码的输出是什么？解释 `Deref` 和 `DerefMut` 的作用

```rust
use std::ops::Deref;

struct MyBox<T>(T);

impl<T> Deref for MyBox<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

fn hello(name: &str) {
    println!("Hello, {name}!");
}

fn main() {
    let m = MyBox(String::from("Rust"));
    hello(&m);
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出 `Hello, Rust!`

**解析**：`Deref` trait 启用**强制解引用（deref coercion）**。

**发生了什么**：

```rust,ignore
hello(&m);
// &MyBox<String> 自动强制转换为 &String（调用 deref）
// &String 再自动强制转换为 &str（String 也实现 Deref<Target=str>）
```

**等价展开**：

```rust,ignore
hello(&(*m)[..]);
// 1. *m     → Deref::deref(&m) → &String
// 2. (*m)[..] → &str（字符串切片）
// 3. &(*m)[..] → &str
```

**规则**：

- `&T` 若 `T: Deref<Target=U>`，可自动转为 `&U`
- `&mut T` 若 `T: DerefMut<Target=U>`，可自动转为 `&mut U`
- 最多连续应用 1 层自动 deref coercion

**标准库中的 `Deref` 实现**：

| 类型 | `Target` | 说明 |
|:---|:---|:---|
| `Box<T>` | `T` | 解引用到堆数据 |
| `Rc<T>` / `Arc<T>` | `T` | 解引用到共享数据 |
| `Vec<T>` | `[T]` | 解引用到切片（Slice） |
| `String` | `str` | 解引用到字符串切片（String Slice） |
| `Cow<'a, T>` | `T` | 写时克隆指针 |

**知识点**：`Deref` 是 Rust 中智能指针（Smart Pointer）"透明化"的关键机制，使智能指针的使用体验接近普通引用。[→ 内存管理详解](03_memory_management.md)

</details>

---

## 六、评分参考

| 得分 | 评价 | 建议 |
|:---:|:---|:---|
| 10/10 | 🏆 内存管理已内化 | 尝试实现自定义智能指针（Smart Pointer）（带 `Deref`/`Drop`） |
| 7–9/10 | ✅ 核心概念掌握 | 用 `Rc<RefCell<T>>` 实现图结构，对比 `Arc<Mutex<T>>` 版本 |
| 4–6/10 | 🔄 需巩固基础 | 重读 [Memory Management](03_memory_management.md)，完成 rustlings 智能指针（Smart Pointer）章节 |
| 0–3/10 | 📚 建议重新开始 | 从 [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) 确认基础，再读内存管理 |

---

> **对应 Crate**: [`c01_ownership_borrow_scope`](../../crates/c01_ownership_borrow_scope)
> **对应练习**: [`exercises/src/ownership_borrowing/ex05_smart_pointer_rc.rs`](../../exercises/src/ownership_borrowing/ex05_smart_pointer_rc.rs)

---

> **权威来源**: [The Rust Programming Language — Ch15](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html) · [Rust Reference — Interior Mutability](https://doc.rust-lang.org/reference/interior-mutability.html) · [Rustonomicon — Memory Layout](https://doc.rust-lang.org/nomicon/)

## 嵌入式测验（Embedded Quiz）

### 测验 1：本文件是 测验：内存管理（L2 试点扩展） 的专项测验集。这类测验文件的主要作用是什么？（理解层）

**题目**: 本文件是 测验：内存管理（L2 试点扩展） 的专项测验集。这类测验文件的主要作用是什么？

<details>
<summary>✅ 答案与解析</summary>

集中提供大量针对特定主题的练习题，帮助学习者系统检验和巩固对该主题的掌握程度，补充概念文件中的嵌入式测验。
</details>

---

### 测验 2：在 测验：内存管理（L2 试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？（理解层）

**题目**: 在 测验：内存管理（L2 试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？

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
