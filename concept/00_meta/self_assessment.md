# Rust 知识体系自测题库（Self-Assessment）

> **定位**：每个层级配套的自测题，用于验证知识掌握程度。答案和解析附在每题之后（可折叠）。
> **使用方式**：先做题，再对答案。建议配合 [`learning_guide.md`](./learning_guide.md) 使用。

---

## L1 基础层：所有权与类型系统（8 题）

### Q1: Move vs Copy

以下代码能否编译？如果不能，为什么？

```rust,compile_fail,E0382
let s1 = String::from("hello");
let s2 = s1;
println!("{}", s1);
```

<details>
<summary>答案</summary>

**不能编译**。`String` 未实现 `Copy`，赋值时发生 Move，`s1` 所有权转移给 `s2`，之后 `s1` 不可用。编译错误 **E0382**。

**修正**：`let s2 = s1.clone();`

</details>

---

### Q2: 借用规则

以下代码能否编译？

```rust,compile_fail,E0502
let mut x = 5;
let r1 = &x;
let r2 = &mut x;
println!("{}", r1);
```

<details>
<summary>答案</summary>

**不能编译**。`r1` 是共享引用 `&x`，`r2` 是可变引用 `&mut x`，二者不能共存。编译错误 **E0502**。

**核心规则**：任意时刻，要么一个 `&mut T`，要么任意多个 `&T`。

</details>

---

### Q3: 生命周期省略

以下函数签名能否编译？为什么？

```rust
fn first_word(s: &str) -> &str {
    &s[0..1]
}
```

<details>
<summary>答案</summary>

**能编译**。满足生命周期省略规则（第1条）：单个输入引用 → 输出引用获得相同生命周期。

完整签名等价于：

```rust
fn first_word<'a>(s: &'a str) -> &'a str
```

</details>

---

### Q4: enum 穷尽匹配

以下 `match` 是否完整？

```rust,compile_fail,E0004
enum Color { Red, Green, Blue }
fn describe(c: Color) -> &'static str {
    match c {
        Color::Red => "red",
        Color::Green => "green",
    }
}
```

<details>
<summary>答案</summary>

**不完整**。缺少 `Color::Blue` 分支，编译错误 **E0004**。

**修正**：添加 `Color::Blue => "blue"` 或使用 `_ => "other"` 通配。

</details>

---

### Q5: Trait 对象安全

以下能否创建 `dyn Drawable`？

```rust
trait Drawable {
    fn draw(&self);
    fn new() -> Self where Self: Sized;
}
```

<details>
<summary>答案</summary>

**能**。`where Self: Sized` 的关联方法不会破坏对象安全性，因为它在 trait object 上不可调用。

如果 `new()` 没有 `where Self: Sized`，则 `dyn Drawable` 不可创建（vtable 无法包含构造方法）。

</details>

---

### Q6: Result 传播

以下代码的问题是什么？

```rust,compile_fail,E0277
fn read_config(path: &str) -> String {
    let contents = std::fs::read_to_string(path)?;
    contents
}
```

<details>
<summary>答案</summary>

**`?` 运算符要求函数返回 `Result<T, E>`**。当前返回类型是 `String`，不匹配。

**修正**：

```rust
fn read_config(path: &str) -> Result<String, std::io::Error> {
    let contents = std::fs::read_to_string(path)?;
    Ok(contents)
}
```

</details>

---

### Q7: Drop 顺序

以下代码的输出顺序是什么？

```rust
struct A(&'static str);
impl Drop for A {
    fn drop(&mut self) { println!("{}", self.0); }
}
let _a = A("a");
{
    let _b = A("b");
}
let _c = A("c");
```

<details>
<summary>答案</summary>

输出顺序：`b` → `a` → `c`

**规则**：变量按与声明相反的顺序 drop（LIFO），`_b` 作用域最小，最先 drop。

</details>

---

### Q8: 泛型单态化

以下代码编译后生成几个版本的 `identity`？

```rust
fn identity<T>(x: T) -> T { x }
let a = identity(5i32);
let b = identity(3.14f64);
let c = identity("hello");
```

<details>
<summary>答案</summary>

**3 个版本**：`identity_i32`、`identity_f64`、`identity_&str`。

Rust 泛型采用**单态化**，每个具体类型生成独立函数体，零运行时开销。

</details>

---

## L2 进阶层：泛型与错误处理（7 题）

### Q9: Trait Bounds

以下代码能否编译？

```rust,compile_fail,E0277
fn print_debug<T>(x: T) {
    println!("{:?}", x);
}
```

<details>
<summary>答案</summary>

**不能**。`println!("{:?}", x)` 要求 `T: Debug`，但函数签名未声明此 bound。编译错误。

**修正**：`fn print_debug<T: std::fmt::Debug>(x: T)`

</details>

---

### Q10: Associated Types vs Generics

`trait Iterator<T>` 和 `trait Iterator { type Item; }` 的区别是什么？

<details>
<summary>答案</summary>

- **泛型参数 `<T>`**：一个类型可实现 `Iterator<i32>` 和 `Iterator<String>`（多实例）
- **关联类型 `type Item`**：一个类型只能实现一次 `Iterator`（单实例）

Iterator 选择关联类型，因为 "一个集合只有一种元素类型" 是符合直觉的约束。

</details>

---

### Q11: PhantomData 用途

为什么以下代码需要 `PhantomData<T>`？

```rust
struct MyPtr<T> {
    ptr: *mut (),
    _marker: std::marker::PhantomData<T>,
}
```

<details>
<summary>答案</summary>

`PhantomData<T>` 告诉编译器：`MyPtr<T>` 逻辑上拥有/关联 `T`，影响：

1. **Drop check**：编译器知道 `MyPtr<T>` 可能需要 drop `T`
2. **Variance**：`MyPtr<T>` 的协变/逆变关系与 `T` 一致
3. **Send/Sync**：自动推导基于 `T`

没有 `PhantomData<T>`，`MyPtr<T>` 对所有 `T` 都是协变的，且总是 `Send + Sync`。

</details>

---

### Q12: RefCell 运行时检查

以下代码运行结果？

```rust
use std::cell::RefCell;
let cell = RefCell::new(0);
let _b1 = cell.borrow();
let _b2 = cell.borrow_mut();  // 运行时 panic
```

<details>
<summary>答案</summary>

**运行时 panic**：`already mutably borrowed`。

`RefCell` 在运行时检查借用规则（而非编译期），检测到共享借用和可变借用共存时 panic。

</details>

---

### Q13: 错误传播转换

`?` 运算符如何转换错误类型？

```rust,compile_fail,E0277
fn foo() -> Result<(), MyError> {
    std::fs::read_to_string("file.txt")?;  // io::Error → MyError ?
}
```

<details>
<summary>答案</summary>

`?` 运算符要求 `From<源错误> for 目标错误` 实现存在。需为 `MyError` 实现：

```rust
impl From<std::io::Error> for MyError { ... }
```

或使用 `map_err` 手动转换。

</details>

---

### Q14: Sized vs ?Sized

以下函数签名有什么问题？

```rust
fn process<T>(data: T) {
    let size = std::mem::size_of::<T>();
}
```

<details>
<summary>答案</summary>

**没有问题**。泛型参数默认 `T: Sized`，`size_of::<T>()` 要求 `T: Sized`，满足。

如果要接受 trait object：`fn process<T: ?Sized>(data: &T)`

</details>

---

### Q15: 闭包捕获

以下闭包捕获 `x` 的方式？

```rust
let x = String::from("hello");
let f = || println!("{}", x);  // 捕获方式？
let g = move || println!("{}", x);  // 捕获方式？
```

<details>
<summary>答案</summary>

- `f`：**不可变引用** `&x`（因为只读）
- `g`：**Move** `x`（`move` 关键字强制转移所有权）

`move` 后 `x` 不可用。

</details>

---

## L3 高级层：并发与异步（8 题）

### Q16: Send + Sync

`Rc<String>` 是 `Send` 还是 `Sync`？为什么？

<details>
<summary>答案</summary>

**既不是 Send 也不是 Sync**。

- `Rc` 使用非原子引用计数，跨线程 clone/drop 会导致数据竞争
- `String` 本身是 `Send + Sync`，但 `Rc` 的包装使其不再线程安全

**多线程共享** → `Arc<String>`

</details>

---

### Q17: MutexGuard 跨 await

以下代码能否编译？

```rust,compile_fail,E0277
async fn fetch_and_update(data: &Mutex<i32>) {
    let mut guard = data.lock().unwrap();
    *guard += fetch_from_network().await;  // await 在 guard 作用域内
}
```

<details>
<summary>答案</summary>

**不能编译**。`MutexGuard` 不是 `Send`，跨 await 时编译器拒绝（因为可能切换到另一个线程执行，而 guard 持有线程本地锁）。

**修正**：缩小 guard 作用域：

```rust
async fn fetch_and_update(data: &Mutex<i32>) {
    let value = fetch_from_network().await;
    let mut guard = data.lock().unwrap();
    *guard += value;
}
```

</details>

---

### Q18: Pin 语义

为什么 `Future::poll` 使用 `Pin<&mut Self>` 而非 `&mut Self`？

<details>
<summary>答案</summary>

`async fn` 编译后的状态机可能包含**自引用字段**（如 `let x = ...; let y = &x;`）。

如果状态机被 Move（`&mut Self` 允许），自引用指针将悬垂。

`Pin` 保证 `Self` 的内存地址不变，保护自引用结构。

</details>

---

### Q19: 死锁条件

以下代码是否可能死锁？

```rust
let a = Mutex::new(0);
let b = Mutex::new(0);
let a2 = Arc::clone(&a);
let b2 = Arc::clone(&b);
thread::spawn(move || {
    let _a = a.lock();
    let _b = b.lock();
});
let _b = b2.lock();
let _a = a2.lock();
```

<details>
<summary>答案</summary>

**可能死锁**。两个线程以**相反顺序**获取锁：

- 线程1：a → b
- 线程2：b → a

**避免**：统一锁获取顺序（如按地址排序），或使用 `std::sync::Mutex::lock` + 超时。

</details>

---

### Q20: unsafe 块边界

`unsafe` 块内部可以使用哪些编译器不检查的操作？

<details>
<summary>答案</summary>

5 个特定逃逸门：

1. 解引用原始指针 `*raw_ptr`
2. 调用 `unsafe fn`
3. 访问 `mut static`
4. 实现 `unsafe trait`
5. 读取 `union` 字段

**注意**：`unsafe` 块不关闭类型系统，类型检查仍然有效。

</details>

---

### Q21: Waker 机制

自定义 Future 为什么需要存储 `Waker`？

<details>
<summary>答案</summary>

当 `poll` 返回 `Pending` 时，Future 被挂起。如果没有存储 Waker，事件就绪时无法通知执行器重新 poll。

**流程**：

1. `poll` 发现未就绪 → 存储 `cx.waker()` → 返回 `Pending`
2. 外部事件就绪 → 调用 `waker.wake()`
3. 执行器将任务重新加入队列 → 再次 `poll`

</details>

---

### Q22: 宏卫生性

以下宏调用输出什么？

```rust
macro_rules! make_var {
    ($name:ident, $val:expr) => {
        let $name = $val;
    };
}
fn main() {
    let x = 10;
    make_var!(x, 20);
    println!("{}", x);
}
```

<details>
<summary>答案</summary>

**输出 10**。

Rust 宏是**卫生宏**：宏内部定义的 `let x` 不会覆盖外部 `x`。宏中的 `x` 是独立命名空间。

</details>

---

### Q23: unsafe 安全契约

以下 `unsafe` 实现是否安全？

```rust
unsafe impl Send for MyType {}
```

<details>
<summary>答案</summary>

**取决于 `MyType` 的字段**。如果 `MyType` 包含 `Rc<T>` 或原始指针，则手动实现 `Send` 可能导致数据竞争。

**原则**：`unsafe impl` 的安全契约由程序员保证，编译器不验证。

</details>

---

## L4 形式化层：类型理论与证明（7 题）

### Q24: 仿射逻辑

Rust 的 Ownership 对应哪种逻辑？

<details>
<summary>答案</summary>

**仿射逻辑（Affine Logic）** — "A resource can be used at most once"。

通过 `weakening` 规则实现 Copy（0 次或 1 次 → 任意次数）。

</details>

---

### Q25: 参数性定理

以下函数的实现必然是什么？

```rust
fn identity<T>(x: T) -> T { ... }
```

<details>
<summary>答案</summary>

**必然返回 `x`**。

根据 **参数性定理（Parametricity）**，没有任何关于 `T` 的信息，函数只能返回输入值（或 panic/diverge）。

</details>

---

### Q26: HRTB

以下 `F` 的 bound 含义？

```rust
fn process<F>(f: F)
where F: for<'a> Fn(&'a str) -> &'a str,
```

<details>
<summary>答案</summary>

**高阶 Trait Bound（HRTB）**：`F` 接受任意生命周期 `'a` 的 `&str` 引用，返回相同生命周期 `'a` 的 `&str`。

等价于 **System F 中的全称量化** `∀'a. (Fn(&'a str) -> &'a str)`。

</details>

---

### Q27: Region-based 内存管理

Rust 生命周期与 Region-based Memory Management 的关系？

<details>
<summary>答案</summary>

Rust 借鉴了 **Region 类型系统**（Tofte & Talpin, 1994）：

- 值绑定到一个区域（lexical scope）
- 区域结束时，区域内所有值被释放
- 但 Rust 的区域是**结构化**的（基于词法作用域），且通过借用检查器验证引用有效性

**区别**：Rust 允许非词法生命周期（NLL），而经典 Region 是纯词法的。

</details>

---

### Q28: Soundness 定义

"Rust 类型系统是 sound" 意味着什么？

<details>
<summary>答案</summary>

**类型安全（Soundness）**：如果程序通过类型检查，则运行时不会出现**未定义行为（UB）**。

形式化定义：**Progress + Preservation**

- **Progress**：良类型表达式不会 stuck（除安全停机外）
- **Preservation**：求值保持类型

</details>

---

### Q29: 分离逻辑

如何用分离逻辑（Separation Logic）表达 "x 指向 5，y 指向 10"？

<details>
<summary>答案</summary>

```
x ↦ 5 ∗ y ↦ 10
```

`∗`（分离合取）表示 `x` 和 `y` 指向**不相交**的内存区域。

</details>

---

### Q30: Oxide 形式化

Oxide 形式化中，`Γ ⊢ e : τ ⊣ Φ` 的 `Φ` 表示什么？

<details>
<summary>答案</summary>

`Φ`（Effect）表示表达式 `e` 执行后的**所有权环境变化**，记录哪些变量被 move、哪些被 borrow。

Oxide 的核心创新：用 **ownership typing** 形式化 Rust 的所有权规则。

</details>

---

## L5 对比层：多语言范式（5 题）

### Q31: Rust vs C++ RAII

Rust 的 RAII 与 C++ 有何根本区别？

<details>
<summary>答案</summary>

- **C++**：Move 是默认的（复制构造函数可被省略），所有权隐含，容易悬垂
- **Rust**：Move 是显式的（`=` 即 move），所有权在类型系统中追踪，编译器保证无悬垂

</details>

---

### Q32: Rust vs Haskell 类型类

Rust Trait 与 Haskell Typeclass 的核心差异？

<details>
<summary>答案</summary>

- **Orphan Rule**：Rust 禁止为外部类型实现外部 Trait（Haskell 允许 `orphan instance`）
- **无高阶类型（HKT）**：Rust 没有 `* -> *` 级别的抽象（可用 GAT 模拟）
- **无类型类推导**：Rust 需要显式 `#[derive]` 或手动实现

</details>

---

### Q33: Rust vs Go 并发模型

Rust 的并发安全如何保障？

<details>
<summary>答案</summary>

- **Rust**：编译期通过 `Send/Sync` Trait 保证，数据竞争是编译错误
- **Go**：运行时通过 `go vet` / `race detector` 检测，竞争条件可能导致运行时错误

Rust 的并发安全是**零运行时开销**的编译期保证。

</details>

---

### Q34: 依赖类型

为什么 Rust 不采用依赖类型？

<details>
<summary>答案</summary>

依赖类型（如 `Vec<n>` 其中 `n` 是类型级自然数）要求：

1. 类型检查可能不可判定（Turing 完备的类型级计算）
2. 类型推断需要 SMT 求解器，编译时间爆炸
3. 与普通程序员的学习曲线冲突

Rust 选择 **Const Generics** 作为折中：编译期已知常量，但保留可判定的类型检查。

</details>

---

### Q35: Linear vs Affine

线性类型系统与仿射类型系统的区别？

<details>
<summary>答案</summary>

- **线性（Linear）**：资源必须**恰好使用 1 次**（no weakening, no contraction）
- **仿射（Affine）**：资源可以**使用 0 次或 1 次**（允许 weakening，不允许 contraction）

Rust 是仿射的：`let x = ...;` 后不使用 `x` 是合法的（ weakening）。

</details>

---

## L6 生态层：工程实践（5 题）

### Q36: Cargo Workspace

Workspace 中 `resolver = "2"` 的作用？

<details>
<summary>答案</summary>

Resolver 2（Rust 2021 默认）按**特性**而非**包**解析依赖：

- 同一个包的不同特性在不同依赖中独立激活
- 避免特性合并导致的编译错误

</details>

---

### Q37: 条件编译

`#[cfg(target_os = "windows")]` 与 `#[cfg(unix)]` 的区别？

<details>
<summary>答案</summary>

- `target_os = "windows"`：仅 Windows
- `unix`：所有 Unix-like 系统（Linux、macOS、BSD 等）

**最佳实践**：优先使用平台能力检测（如 `#[cfg(feature = "serde")]`）而非 OS 检测。

</details>

---

### Q38: Miri 用途

Miri 能检测哪些问题？不能检测哪些？

<details>
<summary>答案</summary>

**能检测**：

- 悬垂指针解引用
- 数据竞争（在单线程 Miri 中模拟检测）
- 未对齐访问
- 违反别名规则

**不能检测**：

- 死锁（无真正的多线程执行）
- 无限循环
- 性能问题

</details>

---

### Q39: Rust 版本兼容性

Rust 如何保证向后兼容？

<details>
<summary>答案</summary>

1. **Edition 系统**：2015/2018/2021/2024，同一 crate 内统一版本
2. **Stability Promise**：稳定 API 永不删除/修改语义
3. **Cargo.lock**：锁定精确版本，防止依赖漂移
4. **SemVer**：遵循语义化版本，minor 版本新增功能，patch 修复 bug

</details>

---

### Q40: unsafe 审计清单

代码审查中 `unsafe` 块需要检查哪些事项？

<details>
<summary>答案</summary>

1. **原始指针有效性**：是否可能悬垂/未对齐/空指针？
2. **别名规则**：是否违反 `&mut T` 的唯一性？
3. **线程安全**：手动 `Send/Sync` 实现是否正确？
4. **边界检查**：切片访问是否越界？
5. **FFI 契约**：C 函数的前置/后置条件是否满足？
6. **panic 安全**：panic 时是否泄漏资源或破坏不变量？

</details>

---

> **评分标准**（自我评估）：
>
> - **34-40 题正确**：L1-L6 全部掌握，可深入 L4 形式化细节
> - **27-33 题正确**：L1-L3 扎实，L4-L6 需针对性补强
> - **20-26 题正确**：L1-L2 基本掌握，建议重读对应章节
> - **<20 题正确**：建议从 [`learning_guide.md`](./learning_guide.md) 基础路径重新开始
>
> **深入阅读**：
>
> - L1-L3 完整理论见 [`semantic_space.md`](./semantic_space.md) §2-3
> - L4 形式化背景见 [`../04_formal/`](../04_formal/)
> - L5 对比见 [`../05_comparative/`](../05_comparative/)
> - L6 实践见 [`../06_ecosystem/`](../06_ecosystem/)

---

### Q41: `Copy` 的边界条件

以下结构体能实现 `Copy` 吗？

```rust,compile_fail,E0204
struct Wrapper<T>(T);

fn main() {
    let w = Wrapper(String::from("hello"));
    let w2 = w;
    println!("{}", w.0);  // 假设 Wrapper 实现了 Copy
}
```

<details>
<summary>答案</summary>

**不能自动实现**。`Wrapper<T>` 要实现 `Copy`，需要 `T: Copy`。`String` 未实现 `Copy`，所以 `Wrapper<String>` 也不能是 `Copy`。

**修正**：`#[derive(Copy, Clone)] struct Wrapper<T: Copy>(T);`

</details>

---

### Q42: 生命周期子类型

以下赋值是否合法？

```rust
let s: &'static str = "hello";
let r: &str = s;
```

<details>
<summary>答案</summary>

**合法**。`'static` 是最长的生命周期，它是所有生命周期的子类型（`'static <: 'a` 对任意 `'a`）。因此 `&'static str` 可以协变为 `&str`。

**关键规则**：生命周期协变——子类型的引用可以赋值给超类型的引用。

</details>

---

### Q43: Trait Bound 的组合

以下代码能否编译？

```rust,compile_fail,E0277
trait Drawable { fn draw(&self); }

fn render<T>(item: T)
where
    T: Drawable + Clone,
{
    let copy = item.clone();
    copy.draw();
}

struct Circle;
impl Drawable for Circle { fn draw(&self) {} }

fn main() {
    render(Circle);
}
```

<details>
<summary>答案</summary>

**不能编译**。`Circle` 实现了 `Drawable`，但没有实现 `Clone`。`T: Drawable + Clone` 要求同时满足两个 bound。

**修正**：`#[derive(Clone)] struct Circle;` 或移除 `Clone` bound。

</details>

---

### Q44: `impl Trait` 的返回类型限制

以下代码的问题是什么？

```rust,compile_fail,E0562
struct MyIter(Vec<i32>);

impl MyIter {
    fn iter(&self) -> impl Iterator<Item = &i32> {
        self.0.iter()
    }
}
```

<details>
<summary>答案</summary>

`impl Trait` 在**结构体方法**中不稳定（需要 RPITIT）。当前 Rust 稳定版不允许在 `impl` 块中使用 `impl Trait` 作为返回类型，除非在 trait 定义中（Rust 1.75+）。

**修正**：显式返回具体类型 `std::slice::Iter<i32>`，或定义 trait 并使用 RPITIT。

</details>

---

### Q45: 内存序的选择

以下代码中 `Relaxed` 内存序是否足够？

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

fn increment() {
    COUNTER.fetch_add(1, Ordering::Relaxed);
}

fn get() -> usize {
    COUNTER.load(Ordering::Relaxed)
}
```

<details>
<summary>答案</summary>

**取决于使用场景**：

- 如果只是计数（不依赖与其他操作的顺序），`Relaxed` **足够**
- 如果需要保证 `increment` 与后续操作的 happens-before 关系，需要 `Release`/`Acquire`
- 如果需要全序一致性（如线程安全初始化），需要 `SeqCst`

`Relaxed` 只保证原子性，不保证顺序一致性。

</details>

---

### Q46: `async trait` 的当前方案

以下代码在 Rust 1.75+ 中能否编译？

```rust
trait AsyncTrait {
    async fn method(&self) -> i32;
}

struct MyStruct;
impl AsyncTrait for MyStruct {
    async fn method(&self) -> i32 { 42 }
}
```

<details>
<summary>答案</summary>

**能编译**（Rust 1.75+）。AFIT（Async Fn In Trait）允许在 trait 中直接定义 `async fn`，编译器自动将返回类型处理为 `impl Future<Output = i32>`。

**限制**：在 Rust 1.75 之前，需要使用 `async-trait` crate 或手动返回 `Pin<Box<dyn Future>>`。

</details>

---

### Q47: `#[repr(C)]` 的用途

为什么 FFI 边界需要使用 `#[repr(C)]`？

```rust
#[repr(C)]
struct Point { x: f64, y: f64 }
```

<details>
<summary>答案</summary>

**原因**：

1. **内存布局**：Rust 默认可以重排字段以优化内存，`#[repr(C)]` 强制按声明顺序布局
2. **ABI 兼容**：C 编译器期望特定的字段顺序和填充规则，`#[repr(C)]` 保证与 C 的互操作性
3. **确定性**：跨语言调用时，双方对结构体内存有相同理解

没有 `#[repr(C)]`，Rust 编译器可能重排 `x` 和 `y` 的顺序，导致 C 代码读取错误。

</details>

---

### Q48: 过程宏的输入输出

过程宏（Procedural Macro）与声明宏（`macro_rules!`）的核心区别是什么？

<details>
<summary>答案</summary>

| 维度 | `macro_rules!` | 过程宏 |
|:---|:---|:---|
| 输入 | Token 流（文本匹配）| Token 流（结构化 AST）|
| 输出 | Token 流 | Token 流 |
| 实现 | 模式匹配 | Rust 函数（`proc_macro` crate）|
| 类型 | 声明宏 | 派生宏 / 属性宏 / 函数式宏 |
| 能力 | 有限（ hygiene 保证）| 完整（可解析、分析、生成任意代码）|

**关键区别**：过程宏在编译期执行 Rust 代码，可以访问 Token 的结构信息；`macro_rules!` 只进行模式匹配和替换。

</details>

---

### Q49: 线性逻辑中的 `!A`

在线性逻辑中，`!A`（指数模态）对应 Rust 的什么概念？

<details>
<summary>答案</summary>

**`!A` 对应 `Copy` trait**。

- 线性逻辑中 `!A` 表示 "A 可以任意复制和使用"（weakening + contraction）
- Rust 中 `T: Copy` 表示 "T 可以按位复制，赋值后原变量仍可用"
- `!A` 将线性资源转化为经典资源，正如 `Copy` 将仿射类型转化为可重用类型

**对比**：

- 严格线性类型：`A` 必须恰好使用 1 次（无 weakening）
- 仿射类型（Rust）：`A` 可以使用 0 次或 1 次（有 weakening，无 contraction）
- `!A` + 仿射：`A` 可以使用任意次数（weakening + contraction）= `Copy`

</details>

---

### Q50: RustBelt 的验证范围

RustBelt 能验证以下哪种属性？

1. Safe Rust 的内存安全
2. `unsafe` 代码块的功能正确性
3. 并发程序无死锁
4. 程序终止性

<details>
<summary>答案</summary>

**只有 1 正确**。

- **✅ 内存安全**：RustBelt 的核心成果——证明 Safe Rust 的 Iris 逻辑模型保证无 UAF/DF
- **❌ unsafe 功能正确性**：RustBelt 不验证 unsafe 块的逻辑，只验证其满足安全契约
- **❌ 无死锁**：活性（liveness）通常不可判定，RustBelt 不证明
- **❌ 终止性**：终止性不是 RustBelt 的验证目标

**关键洞察**：RustBelt 验证的是 **safety**（无坏事情发生），不是 **liveness**（好事情最终发生）。

</details>

---

### Q51: Rust vs C++ 的 ABI 稳定性

Rust 为什么不像 C++ 那样保证 ABI 稳定性？

<details>
<summary>答案</summary>

**原因**：

1. **优化灵活性**：ABI 稳定会限制编译器优化（如字段重排、泛型单态化策略）
2. **Edition 系统**：Rust 用 Edition 而非 ABI 稳定性来管理向后兼容
3. **FFI 边界**：跨语言调用通过 C ABI（`extern "C"`），Rust 内部 ABI 不稳定性不影响 FFI
4. **Cargo 生态**：SemVer + lock 文件管理依赖版本，不需要二进制兼容

**C++ 的代价**：ABI 稳定导致 `std::string` 布局 30 年不变，限制了实现优化。

</details>

---

### Q52: `cargo-deny` 的用途

`cargo-deny` 在供应链安全中起什么作用？

<details>
<summary>答案</summary>

`cargo-deny` 是 Rust 的依赖审计工具，用于：

1. **许可证合规**：检查所有依赖的许可证是否与项目兼容
2. **安全漏洞**：集成 `cargo-audit`，自动检测已知 CVE
3. **依赖限制**：禁止特定 crate、限制依赖深度、检测重复依赖
4. **来源验证**：只允许来自 crates.io 或特定 git 仓库的依赖

**配置示例**：

```toml
[licenses]
allow = ["MIT", "Apache-2.0"]

[advisories]
ignore = ["RUSTSEC-2021-0073"]

[bans]
deny = [{ name = "deprecated-crate" }]
```

</details>

---

> **评分标准更新**（60 题版）：
>
> - **50-60 题正确**：L1-L6 全部掌握，可深入 L4 形式化细节
> - **40-49 题正确**：L1-L3 扎实，L4-L6 需针对性补强
> - **30-39 题正确**：L1-L2 基本掌握，建议重读对应章节
> - **<30 题正确**：建议从 [`learning_guide.md`](./learning_guide.md) 基础路径重新开始

---

### Q53: `Deref` 自动解引用

以下代码输出什么？

```rust
use std::ops::Deref;

struct MyBox<T>(T);

impl<T> Deref for MyBox<T> {
    type Target = T;
    fn deref(&self) -> &T { &self.0 }
}

fn main() {
    let x = MyBox(5);
    println!("{}", *x + 1);
}
```

<details>
<summary>答案</summary>

**输出 `6`**。

`*x` 不是直接解引用指针，而是调用 `x.deref()` 获取 `&i32`，然后解引用得到 `5`。`Deref` 的自动解引用让自定义智能指针的行为像内置引用一样。

**关键规则**：`Deref` 支持无限次自动解引用（`MyBox<MyBox<i32>>` → `&i32`）。

</details>

---

### Q54: `Cow<T>` 的用途

`Cow<'a, str>` 中的 "Clone on Write" 是什么意思？

```rust
use std::borrow::Cow;

fn process(input: &str) -> Cow<str> {
    if input.contains('\t') {
        Cow::Owned(input.replace('\t', "    "))
    } else {
        Cow::Borrowed(input)
    }
}
```

<details>
<summary>答案</summary>

**"Clone on Write"** 表示：

- 如果不需要修改 → 返回借用引用（零分配）
- 如果需要修改 → 克隆数据并返回拥有的值

**用途**：在"可能修改也可能不修改"的场景下避免不必要的内存分配。上例中，如果 `input` 不含 `\t`，直接返回引用；否则创建新的 `String`。

**与 `&str`/`String` 的关系**：`Cow<str>` 是两者的统一抽象。

</details>

---

### Q55: `crossbeam::scope` 的优势

`crossbeam::scope` 相比 `std::thread::spawn` 有什么优势？

```rust
use crossbeam::scope;

fn main() {
    let mut data = [1, 2, 3];
    scope(|s| {
        for x in &mut data {
            s.spawn(move |_| { *x *= 2; });
        }
    });
    println!("{:?}", data);  // [2, 4, 6]
}
```

<details>
<summary>答案</summary>

**优势**：

1. **借用栈数据**：`scope` 中的线程可以借用父作用域的变量（`&mut data`），`std::thread::spawn` 要求 `'static`
2. **自动 join**：`scope` 结束时自动等待所有子线程完成，无需手动 `join`
3. **无泄漏保证**：编译器确保 `scope` 内的线程不会泄漏到外部

**限制**：`scope` 内的线程不能比 `scope` 活得更长（由编译器保证）。

</details>

---

### Q56: `Stream` trait

`Stream` 与 `Iterator` 的核心区别是什么？

<details>
<summary>答案</summary>

| 维度 | `Iterator` | `Stream` |
|:---|:---|:---|
| 同步/异步 | 同步（`next()` 阻塞）| 异步（`poll_next()` 非阻塞）|
| 返回 | `Option<Self::Item>` | `Poll<Option<Self::Item>>` |
| 使用 | `for x in iter` | `while let Some(x) = stream.next().await` |
| 背压 | 无（调用者控制）| 有（通过 `Poll::Pending`）|

**核心区别**：`Stream` 是异步版的 `Iterator`，支持背压和协作式调度。`tokio::sync::mpsc::Receiver` 实现了 `Stream`。

</details>

---

### Q57: 分离逻辑的 `*`（separating conjunction）

`P * Q` 与 `P ∧ Q`（逻辑与）的区别是什么？

<details>
<summary>答案</summary>

| | `P * Q` | `P ∧ Q` |
|:---|:---|:---|
| 含义 | P 和 Q 的内存区域**不相交** | P 和 Q 同时成立 |
| 内存 | 两个断言描述不相交的堆 | 可能重叠 |
| Rust 对应 | `let (x, y) = (a, b);`（两个独立所有权）| `let r1 = &x; let r2 = &x;`（共享引用）|

**关键洞察**：`x ↦ 5 * y ↦ 10` 表示 `x` 和 `y` 指向**不同**的内存地址，这正是 Rust 所有权转移的数学基础。

</details>

---

### Q58: System F 的 `Λ`（大写 lambda）

System F 中的 `Λα.λx:α. x` 在 Rust 中如何表达？

<details>
<summary>答案</summary>

```rust
fn identity<T>(x: T) -> T { x }
```

**对应关系**：

- `Λα` → `<T>`（类型抽象）
- `λx:α` → `fn(x: T)`（值抽象）
- `. x` → `{ x }`（函数体）

**区别**：System F 是纯粹的形式系统，Rust 的泛型会被**单态化**为具体类型，而 System F 保留类型抽象到运行时（如果支持）。

</details>

---

### Q59: `no_std` 下的 `Vec`

在 `#![no_std]` 环境下，为什么还能使用 `Vec<T>`？

<details>
<summary>答案</summary>

**`#![no_std]` 只排除 `std`，不排除 `alloc`**。

- `std` = `core` + `alloc` + 平台特定功能（IO、线程、网络）
- `#![no_std]` 仍然可以 `#![feature(alloc)]` + `extern crate alloc;`
- `Vec<T>`、`String`、`Box<T>` 都在 `alloc` 中定义

**限制**：`no_std` 环境下没有 `std::io`、`std::thread`、`std::net`，需要手动处理或依赖 `libc`。

</details>

---

### Q60: `cargo-vet` 的审计流程

`cargo-vet` 如何确保供应链安全？

<details>
<summary>答案</summary>

`cargo-vet` 是 Mozilla 开发的依赖审计工具，流程：

1. **定义审计标准**：创建 `audit-as-crates-io` 配置，指定哪些 crate 需要审计
2. **执行审计**：检查每个依赖的版本是否已被审计（通过 `supply-chain/audits.toml`）
3. **记录审计结果**：审计者记录 "我检查了 X 版本 Y crate，认为它安全"
4. **CI 集成**：CI 自动检查所有依赖是否有审计记录，拒绝未审计的依赖

**与 `cargo-audit` 的区别**：

- `cargo-audit`：检查已知 CVE（被动）
- `cargo-vet`：要求人工审计（主动）

</details>

---

> **评分标准更新**（60 题版）：
>
> - **50-60 题正确**：L1-L6 全部掌握，可深入 L4 形式化细节
> - **40-49 题正确**：L1-L3 扎实，L4-L6 需针对性补强
> - **30-39 题正确**：L1-L2 基本掌握，建议重读对应章节
> - **<30 题正确**：建议从 [`learning_guide.md`](./learning_guide.md) 基础路径重新开始

---

### Q61: `ManuallyDrop<T>` 的用途

`ManuallyDrop<T>` 与 `mem::forget` 的区别是什么？

```rust
use std::mem::ManuallyDrop;

struct Resource;
impl Drop for Resource {
    fn drop(&mut self) { println!("Dropping!"); }
}

fn main() {
    let mut r = ManuallyDrop::new(Resource);
    // 如何安全地手动 drop？
}
```

<details>
<summary>答案</summary>

**区别**：

- `mem::forget`：永远跳过 `Drop`，无法恢复
- `ManuallyDrop<T>`：允许延迟 `Drop`，但仍然可以在需要时手动调用

**安全手动 drop**：

```rust
unsafe { ManuallyDrop::drop(&mut r); }
```

**使用场景**：

- `Vec::into_raw_parts` 需要控制元素 drop 顺序
- 自定义容器需要精确控制资源释放时机
- `union` 中的值需要显式选择哪个变体执行 drop

</details>

---

### Q62: `try_fold` vs `fold`

`Iterator::try_fold` 与 `fold` 的核心区别？

```rust
let nums = vec![1, 2, 3, 0, 4];
let result: Result<i32, &'static str> = nums.iter()
    .try_fold(1, |acc, &x| {
        if x == 0 { Err("division by zero") }
        else { Ok(acc / x) }
    });
```

<details>
<summary>答案</summary>

**区别**：

- `fold`：**必须遍历全部元素**，返回值是累积结果
- `try_fold`：**提前短路**，如果闭包返回 `Err` 或 `None`，立即停止遍历

**使用场景**：

- `fold`：求和、拼接字符串（需要处理所有元素）
- `try_fold`：查找、验证（遇到第一个错误即可停止）

**返回值**：

- `fold` → `B`（累积类型）
- `try_fold` → `Result<B, E>` 或 `Option<B>`

</details>

---

### Q63: `loom` 并发模型检测

`loom` 与 Miri 在并发检测上的区别？

<details>
<summary>答案</summary>

| 维度 | `loom` | Miri |
|:---|:---|:---|
| 检测目标 | 并发 bug（数据竞争、死锁、原子序错误）| 未定义行为（UB）|
| 方法 | 枚举所有可能的线程交错 | 解释执行，检测内存违规 |
| 范围 | 用户指定的并发原语 | 完整的 Rust 语义 |
| 性能 | 状态空间爆炸（需限制）| 慢（解释执行）|
| 使用场景 | 测试自定义同步原语 | 验证 unsafe 代码 |

**关键区别**：`loom` 专门用于检测并发算法在所有可能交错下的正确性；Miri 检测更广义的 UB（包括别名违规）。

</details>

---

### Q64: `pin-project` crate

为什么需要 `pin-project` 而不是手动实现 `Pin` 的投影？

<details>
<summary>答案</summary>

**手动实现的问题**：

```rust
// 错误实现！
fn project(self: Pin<&mut Self>) -> Pin<&mut T> {
    unsafe { Pin::new_unchecked(&mut self.field) }
    // 如果 Self 是 Unpin，field 可能被 move！
}
```

**`pin-project` 的作用**：

1. **宏自动生成**：`#[pin_project]` 自动为结构体生成安全的投影方法
2. **Unpin 边界检查**：确保只有 `!Unpin` 的字段才被固定
3. **Drop 保证**：自动生成安全的 `Drop` 实现，避免破坏 Pin 契约

**核心原则**：`pin-project` 消除了手写 `Pin` 投影中的常见错误模式。

</details>

---

### Q65: 仿射逻辑 vs 线性逻辑

Rust 是仿射类型系统而非线性类型系统，关键区别是什么？

<details>
<summary>答案</summary>

| | 线性逻辑 | 仿射逻辑 | Rust |
|:---|:---|:---|:---|
| **weakening** | ❌ 禁止丢弃 | ✅ 允许丢弃 | ✅ `let x = ...;` 后不用 `x` 合法 |
| **contraction** | ❌ 禁止复制 | ❌ 禁止复制 | ❌ Move 语义 |
| **Copy** | 需显式 `!A` | 需显式 `!A` | `#[derive(Copy)]` |

**关键区别**：

- **线性**：资源**必须恰好使用 1 次**（no weakening, no contraction）
- **仿射**：资源**可以使用 0 次或 1 次**（allow weakening, no contraction）

Rust 是仿射的：`let x = String::new();` 后不使用 `x` 是合法的（weakening），但 `let y = x; let z = x;` 不合法（no contraction，除非 `Copy`）。

</details>

---

### Q66: Curry-Howard 对应

"类型即命题，程序即证明" 在 Rust 中如何体现？

<details>
<summary>答案</summary>

**Curry-Howard 对应**：

| 逻辑 | 类型 | Rust 示例 |
|:---|:---|:---|
| 命题 A | 类型 `A` | `i32` |
| 证明 A | `A` 的值 | `5` |
| A → B | 函数 `A -> B` | `fn f(x: A) -> B` |
| A ∧ B | 元组 `(A, B)` | `(i32, String)` |
| A ∨ B | `enum`（和类型）| `Option<T>` = `None` ∨ `Some(T)` |
| ⊥（矛盾）| `!`（never type）| `fn diverge() -> !` |
| 证明存在 | `impl Trait` / `dyn Trait` | `Box<dyn Drawable>` |

**Rust 的体现**：

- `enum Result<T, E>` = `Ok(T)` ∨ `Err(E)` —— 错误处理作为逻辑或
- `match` 穷尽检查 —— 编译器验证所有可能情况都被处理（证明完整性）

</details>

---

### Q67: `cargo-bloat` 的用途

如何分析 Rust 二进制文件的体积膨胀来源？

<details>
<summary>答案</summary>

```bash
cargo bloat --release --crates
```

**输出示例**：

```
File  .text     Size        Crate Name
0.5%   2.4%  12.5KiB        serde serde::de::impls::<impl serde::de::Deserialize for...)
0.3%   1.5%   7.8KiB        regex regex::exec::ExecBuilder::build
```

**用途**：

1. **识别体积大户**：找出占用最多空间的函数和 crate
2. **优化编译**：`strip`、LTO、codegen-units=1
3. **依赖审计**：发现未使用的重量级依赖

**优化策略**：

- `opt-level = "z"`（体积优化）
- `lto = true`（链接时优化）
- `strip = true`（去除符号表）

</details>

---

### Q68: Rust 2024 Edition 的关键变更

Rust 2024 Edition 的主要变更有哪些？

<details>
<summary>答案</summary>

**关键变更**：

| 变更 | 说明 | 影响 |
|:---|:---|:---|
| `gen` 关键字 | 生成器（coroutine）语法 | 新的异步/迭代抽象 |
| `never_type` 稳定 | `!` 类型正式可用 | 更精确的类型表达 |
| `impl Trait` 在 let 绑定 | `let x: impl Trait = ...` | 局部存在类型 |
| `if let` 链 | `if let Some(x) = a && let Some(y) = b` | 更简洁的模式匹配 |
| 保留 `gen` | 禁止用 `gen` 作为标识符 | 破坏性变更（Edition 隔离）|

**Edition 系统**：

- 同一 crate 内统一 Edition
- 依赖可以使用不同 Edition
- 升级 Edition 只需修改 `Cargo.toml`，不需要修改代码（大多数情况下）

</details>

---

### Q69: `TypeId` 的局限性

`std::any::TypeId` 在动态类型检查中的局限性？

```rust
use std::any::{Any, TypeId};

fn main() {
    let a: &dyn Any = &42i32;
    println!("{:?}", a.type_id() == TypeId::of::<i32>()); // true
}
```

<details>
<summary>答案</summary>

**局限性**：

1. **生命周期擦除**：`TypeId` 不包含生命周期信息，`&'a str` 和 `&'b str` 的 `TypeId` 相同
2. **泛型单态化**：`Vec<i32>` 和 `Vec<u32>` 的 `TypeId` 不同（正确）
3. **非 `'static`**：`TypeId::of::<T>()` 要求 `T: 'static`，无法用于引用类型
4. **跨编译器不稳定**：`TypeId` 的具体值在不同编译器版本间可能变化

**安全使用**：仅用于 `dyn Any` 的 `downcast_ref`，不用于持久化存储或跨进程通信。

</details>

---

### Q70: `ThinLTO` vs `FatLTO`

`[profile.release] lto = "thin"` 与 `lto = true` 的区别？

<details>
<summary>答案</summary>

| 维度 | ThinLTO | FatLTO (Full LTO) |
|:---|:---|:---|
| 编译时间 | 快（增量）| 慢（全链接）|
| 二进制体积 | 较大 | 最小 |
| 运行时性能 | 接近 FatLTO | 最优 |
| 内存使用 | 低 | 高（可能 OOM）|
| 适用场景 | 大型项目 | 小型项目 / 最终发布 |

**工作原理**：

- **FatLTO**：所有 IR 加载到内存，全局优化后生成单个模块
- **ThinLTO**：每个 crate 独立优化，跨模块内联通过摘要信息完成

**推荐**：

- 开发/CI：`lto = "thin"`
- 最终发布：`lto = true`（或 `lto = "fat"`）

</details>

---

### Q71: `rustc` 的查询系统

`rustc` 的 "基于查询的编译" 与传统编译器有什么区别？

<details>
<summary>答案</summary>

**传统编译器**：

```
源代码 → 词法分析 → 语法分析 → 类型检查 → 代码生成
```

线性流程，每次修改需要重新编译整个文件。

**rustc 查询系统**：

```
查询图：type_check(fn) → resolve_names(fn) → parse_file(fn)
           ↓
        增量编译：只重新执行受影响的查询
```

**优势**：

1. **增量编译**：修改单个函数只重新编译相关查询
2. **并行化**：无依赖的查询可以并行执行
3. **缓存**：查询结果持久化到磁盘（`target/debug/.fingerprint`）

**查询示例**：`type_of(def_id)`、`borrowck(def_id)`、`mir_built(def_id)`

</details>

---

### Q72: `cranelift` 后端

`rustc` 的 Cranelift 后端与 LLVM 后端有什么区别？

<details>
<summary>答案</summary>

| 维度 | Cranelift | LLVM |
|:---|:---|:---|
| 编译速度 | 快（debug 构建快 20-30%）| 慢（优化更激进）|
| 优化级别 | 基本优化 | 激进优化 |
| 调试体验 | 更好（更准确的 debuginfo）| 良好 |
| 使用场景 | Debug 构建、测试 | Release 构建 |
| 启用方式 | `-Zcodegen-backend=cranelift`（nightly）| 默认 |

**原理**：Cranelift 是 Wasmtime 的代码生成器，设计目标是最小化编译延迟，而非最大化运行时性能。

**推荐**：日常开发使用 Cranelift（若 nightly 可用），发布使用 LLVM。

</details>

---

### Q73: `const` 泛型的表达式

以下代码能否编译？

```rust
struct Array<T, const N: usize>([T; N * 2]);
```

<details>
<summary>答案</summary>

**能编译**（Rust 1.79+）。Const Generics 支持简单的算术表达式：

```rust
struct Array<T, const N: usize>([T; N * 2]);  // ✅
struct Matrix<T, const N: usize>([[T; N]; N]); // ✅
```

**限制**：

- 表达式必须可在编译期求值
- 不支持复杂控制流（`if`、`loop`）
- 需要 `#![feature(generic_const_exprs)]` 用于更复杂的表达式（不稳定）

</details>

---

### Q74: `let-else` 语法

`let-else` 与 `if let` 的区别？

```rust
let Some(x) = opt else {
    return;
};
// x 在此作用域可用
```

<details>
<summary>答案</summary>

**区别**：

| | `let-else` | `if let` |
|:---|:---|:---|
| 绑定范围 | `else` 块后仍可用 | 只在 `if` 块内可用 |
| 提前返回 | 适合 `else { return; }` | 需要嵌套或额外处理 |
| 可读性 | 减少缩进 | 传统方式 |

**使用场景**：

```rust
// let-else: 简洁
let Some(config) = load_config() else {
    bail!("config not found");
};
use_config(config);

// if let: 嵌套
if let Some(config) = load_config() {
    use_config(config);
} else {
    bail!("config not found");
}
```

</details>

---

### Q75: `std::backtrace::Backtrace`

如何在自定义错误类型中捕获堆栈跟踪？

<details>
<summary>答案</summary>

```rust
use std::backtrace::Backtrace;

#[derive(Debug)]
struct MyError {
    msg: String,
    backtrace: Backtrace,
}

impl MyError {
    fn new(msg: &str) -> Self {
        Self {
            msg: msg.to_string(),
            backtrace: Backtrace::capture(),
        }
    }
}
```

**要求**：

- `RUST_BACKTRACE=1` 环境变量启用
- 需要 `std`（`no_std` 不支持）
- 有运行时开销，仅在调试/错误报告中使用

**替代方案**：`thiserror` + `#[backtrace]` 自动集成。

</details>

---

### Q76: `target_feature`

`#[target_feature(enable = "sse2")]` 的作用和风险？

<details>
<summary>答案</summary>

**作用**：为特定函数启用 CPU 特性（SIMD、AVX 等），编译器生成对应指令。

```rust
#[target_feature(enable = "sse2")]
unsafe fn simd_add(a: &[f32], b: &[f32]) -> Vec<f32> {
    // 使用 SSE2 指令
}
```

**风险**：

1. **UB 风险**：在不支持该特性的 CPU 上调用 → 非法指令异常
2. **必须 `unsafe`**：调用者需保证目标平台支持
3. **运行时检测**：应先用 `is_x86_feature_detected!("sse2")` 检查

**安全模式**：

```rust
if is_x86_feature_detected!("avx2") {
    unsafe { avx2_optimized() }
} else {
    fallback()
}
```

</details>

---

### Q77: `std::alloc::GlobalAlloc`

如何实现自定义全局分配器？

<details>
<summary>答案</summary>

```rust
use std::alloc::{GlobalAlloc, Layout, System};

struct LoggingAllocator;

unsafe impl GlobalAlloc for LoggingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = System.alloc(layout);
        eprintln!("alloc: {:?} size={}", ptr, layout.size());
        ptr
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        eprintln!("dealloc: {:?} size={}", ptr, layout.size());
        System.dealloc(ptr, layout);
    }
}

#[global_allocator]
static ALLOCATOR: LoggingAllocator = LoggingAllocator;
```

**要求**：

- 必须实现 `GlobalAlloc` trait
- 必须用 `#[global_allocator]` 标记
- 只能有一个全局分配器
- `unsafe impl` 需保证线程安全和内存对齐

</details>

---

### Q78: `wasm-bindgen` 的工作原理

`wasm-bindgen` 如何实现 Rust 与 JavaScript 的互操作？

<details>
<summary>答案</summary>

**工作原理**：

1. **宏生成绑定**：`#[wasm_bindgen]` 宏在编译期生成 JavaScript 胶水代码
2. **WASM 模块导出**：Rust 函数编译为 WASM 导出函数
3. **JS 包装器**：生成的 JS 代码处理类型转换（`String` ↔ `JSString`、`Vec` ↔ `Array`）
4. **内存共享**：通过 WASM 线性内存在 JS 和 Rust 间传递数据

**示例**：

```rust
#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}
```

生成：

```javascript
export function greet(name) {
    // ... 内存分配、字符串编码、调用 WASM ...
}
```

</details>

---

### Q79: `ripgrep` 的设计哲学

为什么 `ripgrep`（`rg`）比 `grep` 快？

<details>
<summary>答案</summary>

**核心原因**：

1. **默认递归 + 自动忽略**：遵循 `.gitignore`，跳过 `node_modules/` 等目录
2. **并行搜索**：使用 `rayon` 数据并行，多线程搜索多个文件
3. **内存映射**：大文件使用 `mmap` 而非逐行读取
4. **SIMD 优化**：使用 `bytecount` 和 SIMD 加速行尾检测
5. **Rust 的性能**：零成本抽象 + 无 GC 停顿

**设计哲学**：

- "做正确的事"：默认行为符合开发者预期
- "快"：利用 Rust 的并行和 SIMD 能力
- "简单"：单一工具替代 `grep` + `find` + `ack`

</details>

---

### Q80: Rust 学习路径的终极目标

掌握 Rust 知识体系后，如何持续进阶？

<details>
<summary>答案</summary>

**进阶路径**：

| 阶段 | 目标 | 资源 |
|:---|:---|:---|
| **Contributor** | 为 Rust 标准库/核心 crate 贡献 PR | [rustc-dev-guide] |
| **Unsafe 专家** | 编写安全的 FFI 和底层抽象 | [Rustonomicon] |
| **形式化** | 理解 RustBelt、参与 Miri 开发 | [PL 课程] |
| **编译器** | 参与 rustc 开发 | [rustc-dev-guide] |
| **生态系统** | 维护关键 crate（tokio、serde 等）| [Rust API Guidelines] |

**持续学习**：

1. **跟踪 RFC**：关注 rust-lang/rfcs 仓库
2. **参与讨论**：Rust Internals 论坛
3. **阅读源码**：标准库、tokio、rayon 等高质量代码
4. **写博客**：教别人是最好的学习方式

> **最终目标**：不仅会用 Rust，还要理解 "为什么 Rust 是这样设计的"。

</details>

---

> **评分标准**（80 题完整版）：
>
> - **70-80 题正确**：L1-L6 全部掌握，具备贡献 Rust 生态的能力
> - **55-69 题正确**：L1-L3 扎实，L4-L6 需针对性补强
> - **40-54 题正确**：L1-L2 基本掌握，建议重读对应章节
> - **<40 题正确**：建议从 [`learning_guide.md`](./learning_guide.md) 基础路径重新开始
>
> **深入阅读**：
>
> - L1-L3 完整理论见 [`semantic_space.md`](./semantic_space.md)
> - L4 形式化背景见 [`../04_formal/`](../04_formal/)
> - L5 对比见 [`../05_comparative/`](../05_comparative/)
> - L6 实践见 [`../06_ecosystem/`](../06_ecosystem/)
> - L7 演进见 [`../07_future/`](../07_future/)
