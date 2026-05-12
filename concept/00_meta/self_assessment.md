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

rust,ignore
fn first_word<'a>(s: &'a str) -> &'a str
```

</details>

---

### Q4: enum 穷尽匹配

以下 `match` 是否完整？

rust,ignore
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

rust,ignore
fn foo() -> Result<(), MyError> {
    std::fs::read_to_string("file.txt")?;  // io::Error → MyError ?
}
```

<details>
<summary>答案</summary>

`?` 运算符要求 `From<源错误> for 目标错误` 实现存在。需为 `MyError` 实现：

rust,ignore
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

```rust,ignore
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

rust,ignore
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

## L1 扩展层：所有权与类型系统（8 题）

### Q41: 函数参数传递

以下代码能否编译？

```rust
fn take(s: String) -> String { s }
fn main() {
    let s = String::from("hello");
    let s2 = take(s);
    println!("{}", s);
}
```

<details>
<summary>答案</summary>

**不能编译**。`take(s)` 将 `s` 的所有权 move 进函数，之后 `s` 不可用。编译错误 **E0382**。

**修正**：`take(s.clone())` 或修改 `take` 接收 `&str`。

</details>

---

### Q42: Copy 边界

以下哪些类型自动实现 `Copy`？

```rust
struct Point(i32, i32);
struct Wrapper(String);
enum Opt { Some(i32), None }
```

<details>
<summary>答案</summary>

- `Point`：**是**（所有字段都是 `Copy`）
- `Wrapper`：**否**（`String` 不是 `Copy`）
- `Opt`：**是**（所有变体的数据都是 `Copy`）

`Copy` 是自动推导的，只要所有字段都实现 `Copy`，复合类型就自动实现 `Copy`。

</details>

---

### Q43: 多输入引用生命周期

以下函数签名省略了什么？

rust,ignore
fn longest(x: &str, y: &str) -> &str {
    if x.len() > y.len() { x } else { y }
}
```

<details>
<summary>答案</summary>

**不能编译**。多输入引用时，生命周期省略规则**不适用**，必须显式标注：

rust,ignore
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str
```

编译器无法确定返回引用依赖 `x` 还是 `y`。

</details>

---

### Q44: 字符串切片生命周期

以下代码能否编译？

```rust
fn first_char(s: &String) -> &str {
    &s[0..1]
}
```

<details>
<summary>答案</summary>

**能编译**，但**不推荐**。返回 `&str` 的生命周期与输入 `&String` 相同。

更地道的签名是 `fn first_char(s: &str) -> &str`，接受更广泛的输入（`String` 和 `&str` 都可自动解引用）。

</details>

---

### Q45: enum 内存布局

```rust,ignore
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
}
```

`Message::Quit` 占多少字节？

<details>
<summary>答案</summary>

`Message` 的大小等于最大变体的大小加上判别式（tag）。

- `Quit`：0 字节（单元变体）
- `Move`：8 字节（两个 `i32`）
- `Write`：24 字节（`String` 在 64 位平台）

所以 `Message` 大小为 **24 + tag**（通常 1-8 字节，对齐后为 32 字节）。

</details>

---

### Q46: 类型推断与 Turbofish

以下代码的问题是什么？

```rust,ignore
let v = Vec::new();
v.push(1);
```

<details>
<summary>答案</summary>

**不能编译**。`Vec::new()` 无法推断类型参数 `T`。

**修正**：

```rust
let v: Vec<i32> = Vec::new();
// 或
let v = Vec::<i32>::new();  // turbofish
// 或
let mut v = Vec::new();
v.push(1);  // 从 push 参数推断
```

注意：`v` 必须是 `mut`。

</details>

---

### Q47: match 绑定模式

以下代码输出什么？

```rust
let x = Some(String::from("hello"));
match x {
    Some(ref s) => println!("{}", s),
    None => {},
}
println!("{:?}", x);
```

<details>
<summary>答案</summary>

**输出 `hello`，然后 `Some("hello")`**。

`ref s` 绑定的是对内部值的**引用**，而不是 move 内部值。因此 `x` 仍然有效。

与 `Some(s)` 不同，后者会 move `String`，导致 `x` 不可用。

</details>

---

### Q48: const 上下文限制

以下代码能否编译？

```rust
const fn sum(a: i32, b: i32) -> i32 {
    let v = vec![a, b];
    v.iter().sum()
}
```

<details>
<summary>答案</summary>

**不能编译**。`const fn` 中不能调用 `vec!`（分配堆内存）或 `iter()`（非常量操作）。

`const fn` 只能执行：

- 基本算术和逻辑运算
- `if`/`match` 控制流
- 调用其他 `const fn`
- 从 Rust 1.46 起：部分 `loop` 和 `while`

</details>

---

## L2 扩展层：Trait、泛型、内存管理与错误处理（8 题）

### Q49: Trait Bound 组合

以下 bound 的含义？

```rust
fn process<T>(item: T)
where
    T: Clone + Send + 'static,
{}
```

<details>
<summary>答案</summary>

`T` 必须同时满足：

- `Clone`：可复制
- `Send`：可跨线程传递
- `'static`：不含非 `'static` 引用（即可拥有或 'static 引用）

`+` 表示**交集**：类型必须实现所有列出的 trait 和生命周期约束。

</details>

---

### Q50: Associated Type 约束

以下代码的含义？

```rust
trait Container {
    type Item;
    fn get(&self) -> Option<Self::Item>;
}

fn first<C: Container<Item = i32>>(c: &C) -> Option<i32> {
    c.get()
}
```

<details>
<summary>答案</summary>

`Container<Item = i32>` 是**关联类型等式约束**：要求 `C` 的 `Item` 必须是 `i32`。

这与泛型参数 `Container<i32>` 不同：关联类型每个实现只能有一个，泛型参数可以有多个实例。

</details>

---

### Q51: 结构体生命周期

以下结构体定义是否正确？

```rust
struct Parser<'a> {
    text: &'a str,
    pos: usize,
}
```

<details>
<summary>答案</summary>

**正确**。`Parser` 持有对 `str` 的引用，必须标注生命周期 `'a`。

使用示例：

```rust,ignore
let text = "hello";
let p = Parser { text, pos: 0 };
// p 的生命周期不能超过 text
```

若 `text` 是 `String` 而非 `&str`，则不需要生命周期参数。

</details>

---

### Q52: Drop 与 Panic 安全

以下代码是否 panic 安全？

```rust
struct Guard(Vec<i32>);
impl Drop for Guard {
    fn drop(&mut self) {
        self.0.push(999);
    }
}
```

<details>
<summary>答案</summary>

**不安全（unsound）**。`Drop::drop` 在 panic 展开时也可能被调用，而此时堆可能处于不一致状态。

更关键的是：`drop` 中不应调用可能 panic 的操作（如 `push`，可能在容量不足时分配失败并 panic）。

**原则**：`drop` 实现应保证**不 panic**、**不无限循环**、**不死锁**。

</details>

---

### Q53: Cow 的用途

`std::borrow::Cow` 的用途是什么？

```rust
use std::borrow::Cow;
fn maybe_uppercase(s: &str) -> Cow<'_, str> {
    if s.chars().any(|c| c.is_lowercase()) {
        Cow::Owned(s.to_uppercase())
    } else {
        Cow::Borrowed(s)
    }
}
```

<details>
<summary>答案</summary>

**Clone on Write**：在需要修改时克隆，否则借用。

- 如果输入已满足条件（无需修改）：**零分配**，返回借用
- 如果需要修改：**分配一次**，返回拥有的数据

适用于"可能修改、可能不修改"的场景，避免不必要的克隆。

</details>

---

### Q54: Error Source Chain

以下代码如何遍历错误链？

```rust
use std::error::Error;
fn cause_chain(e: &dyn Error) {
    // 如何打印 e 及其所有 source？
}
```

<details>
<summary>答案</summary>

```rust
fn cause_chain(e: &dyn Error) {
    let mut current: Option<&dyn Error> = Some(e);
    while let Some(err) = current {
        println!("{}", err);
        current = err.source();
    }
}
```

Rust 1.37+：`Error::source()` 替代已弃用的 `Error::cause()`。

或使用迭代器风格：

rust,ignore
std::iter::successors(Some(e), |e| e.source())
    .for_each(|e| println!("{}", e));
```

</details>

---

### Q55: 泛型 vs Trait Object 错误处理

`Result<T, Box<dyn Error>>` 与 `Result<T, impl Error>` 的区别？

<details>
<summary>答案</summary>

- `Box<dyn Error>`：**动态分发**，运行时确定具体错误类型，允许同一函数返回不同错误类型
- `impl Error`：**静态分发**（仅在 RPIT 中可用），编译期单态化，零运行时开销

`Box<dyn Error>` 更灵活但有一次堆分配；`impl Error` 更高效但要求编译期确定类型。

</details>

---

### Q56: Zero-Sized Types (ZST)

以下类型的大小是多少？

```rust
struct Unit;
struct Pair(Unit, Unit);
enum Void {}
```

<details>
<summary>答案</summary>

| 类型 | 大小 |
|:---|:---|
| `Unit` | **0 字节** |
| `Pair` | **0 字节** |
| `Void` | **0 字节**（但无法构造）|

ZST 在运行时不占内存，但编译期类型信息完整。常用于**类型标记**（如 `PhantomData`）或**编译期状态机**。

</details>

---

## L3 扩展层：并发、异步、unsafe 与宏（8 题）

### Q57: Atomic Ordering

`Relaxed`、`Acquire`、`Release`、`SeqCst` 的适用场景？

<details>
<summary>答案</summary>

| Ordering | 场景 |
|:---|:---|
| `Relaxed` | 仅需要原子性，无同步需求（如计数器）|
| `Acquire` | 读操作，需看到之前的 Release 写入（如锁获取）|
| `Release` | 写操作，需保证之前的写入对 Acquire 读可见（如锁释放）|
| `AcqRel` | 读-修改-写操作（如 `fetch_add`）|
| `SeqCst` | 全局顺序一致性（最严格，性能最差）|

**原则**：使用能满足需求的最弱 ordering，以获得最佳性能。

</details>

---

### Q58: Stream vs Iterator

`Stream` 与 `Iterator` 的核心区别？

<details>
<summary>答案</summary>

- `Iterator`：**同步拉取**（`next()` 立即返回 `Option<Item>`）
- `Stream`：**异步拉取**（`next().await` 可能挂起等待数据）

`Stream` 是异步版的 `Iterator`，用于处理异步数据源（如网络流、消息队列）。

rust,ignore
use futures::StreamExt;
while let Some(item) = stream.next().await {
    // 处理 item
}
```

</details>

---

### Q59: Cancel Safety

以下 `select!` 调用是否 cancel-safe？

rust,ignore
loop {
    tokio::select! {
        val = rx.recv() => { println!("{:?}", val); }
        _ = tokio::time::sleep(Duration::from_secs(1)) => {}
    }
}
```

<details>
<summary>答案</summary>

**是**。`tokio::sync::mpsc::Receiver::recv` 是 **cancel-safe** 的：如果 `sleep` 先完成，`recv` future 被 drop 不会丢失消息。

**非 cancel-safe 示例**：`tokio::io::AsyncReadExt::read` 被 cancel 后，部分读取的数据丢失。

**原则**：在 `select!` 中优先使用 cancel-safe 的操作，或对非 cancel-safe 操作使用 `tokio::sync::Semaphore` 等保护。

</details>

---

### Q60: UnsafeCell

`UnsafeCell<T>` 的作用是什么？以下代码是否安全？

```rust
use std::cell::UnsafeCell;
let cell = UnsafeCell::new(5);
unsafe {
    *cell.get() += 1;
}
```

<details>
<summary>答案</summary>

`UnsafeCell<T>` 是 Rust 内部可变性的**核心原语**：它告诉编译器 `T` 可能有别名且会被修改，禁用 `&T` 的不可变假设。

这段代码**安全**（虽然使用了 `unsafe` 块）：单线程下通过 `UnsafeCell::get()` 获取 `*mut T` 并修改是合法的。

但多线程下仍需 `Sync` 保证，通常使用 `Mutex<T>` 或 `Atomic*` 包装。

</details>

---

### Q61: Strict Provenance

`ptr::addr()` 和 `ptr::with_addr()` 的作用？

<details>
<summary>答案</summary>

**Strict Provenance** 是 Rust 对指针别名规则的严格化：

- `ptr::addr()`：获取指针的**地址**（整数），**丢弃 provenance**
- `ptr::with_addr(addr)`：用新地址构造指针，**继承原指针的 provenance**

**禁止**：`ptr as usize as *mut T`（丢失 provenance 信息）

**允许**：

```rust,ignore
let addr = ptr.addr();
let new_ptr = ptr.with_addr(addr + 4);
```

这对编译器优化和 Miri 检测 UB 至关重要。

</details>

---

### Q62: Proc Macro Hygiene

以下 proc macro 生成的代码是否合法？

```rust
// proc macro
quote! {
    let x = 42;
    println!("{}", x);
}
// 调用处
let x = 10;
my_macro!();
println!("{}", x);
```

<details>
<summary>答案</summary>

**合法**。Proc macro 生成的标识符具有**独立 hygiene**，不会与调用处的 `x` 冲突。

输出 `42` 后，调用处的 `x` 仍是 `10`。

这与 `macro_rules!` 的 hygiene 类似，但 proc macro 的 hygiene 在 token 级别由编译器管理。

</details>

---

### Q63: Pin Projection

以下代码的问题？

```rust
struct MyFuture {
    data: String,
    pointer: *const String,
}
impl Future for MyFuture {
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        unsafe {
            println!("{}", &*self.pointer);
        }
        Poll::Ready(())
    }
}
```

<details>
<summary>答案</summary>

**未使用 Pin projection**。`self: Pin<&mut Self>` 不能直接获取 `&mut self.data`，因为 `MyFuture` 可能已被固定。

**修正**：使用 `pin_project` 或手动 unsafe projection：

rust,ignore
fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = unsafe { self.get_unchecked_mut() };
    // 现在可以安全访问 this.data 和 this.pointer
}
```

必须保证被投影的字段不会移动。

</details>

---

### Q64: Send 推导

以下类型是否自动实现 `Send`？

```rust
struct Wrapper<T>(T);
struct BadWrapper(*const u8);
```

<details>
<summary>答案</summary>

- `Wrapper<T>`：**自动实现** `Send`（当 `T: Send` 时）。编译器自动为仅包含 `Send` 字段的结构体推导 `Send`。
- `BadWrapper`：**不自动实现** `Send`。原始指针 `*const u8` 不是 `Send`，因此 `BadWrapper` 默认不是 `Send`。

可以手动 `unsafe impl Send for BadWrapper {}`，但需确保线程安全。

</details>

---

## L4 扩展层：线性逻辑、类型论、所有权形式化与 RustBelt（8 题）

### Q65: 子结构逻辑

线性逻辑（Linear）、仿射逻辑（Affine）、相关逻辑（Relevant）的区别？Rust 属于哪种？

<details>
<summary>答案</summary>

| 逻辑 | Weakening（丢弃） | Contraction（复制） | Rust 对应 |
|:---|:---|:---|:---|
| 线性 | ❌ 禁止丢弃 | ❌ 禁止复制 | `Linear`（严格使用 1 次）|
| 仿射 | ✅ 允许丢弃 | ❌ 禁止复制 | **Rust 所有权**（使用 0 或 1 次）|
| 相关 | ❌ 禁止丢弃 | ✅ 允许复制 | `Copy` 类型（必须至少使用 1 次）|
| 经典 | ✅ | ✅ | 传统 GC 语言 |

Rust 是**仿射类型系统**：允许丢弃（`let x = ...;` 后不用 `x` 合法），但不允许隐式复制（需显式 `.clone()` 或实现 `Copy`）。

</details>

---

### Q66: Curry-Howard 同构

Curry-Howard 同构在 Rust 中的体现？

<details>
<summary>答案</summary>

Curry-Howard 同构：类型 ↔ 命题，程序 ↔ 证明。

| 逻辑 | Rust |
|:---|:---|
| `A → B`（蕴含）| `fn(A) -> B` |
| `A ∧ B`（合取）| `(A, B)` |
| `A ∨ B`（析取）| `enum { A, B }` |
| `⊥`（矛盾）| `!`（never type）|
| `∀X. P(X)` | `fn<T>() -> P<T>` |

Rust 的 `match` 穷尽性检查对应**排中律的构造性解释**：必须提供所有分支的证明。

</details>

---

### Q67: Type Soundness vs Memory Safety

"Rust 类型系统是 sound 的" 与 "Rust 保证内存安全" 是同一回事吗？

<details>
<summary>答案</summary>

**不是同一回事**。

- **Type Soundness**：良类型程序不会 stuck（除安全停机外），即 Progress + Preservation
- **Memory Safety**：程序不会出现 use-after-free、数据竞争、缓冲区溢出等

Rust 的 type soundness 保证 memory safety **在 safe Rust 中**。但在 `unsafe` 块中，type soundness 假设可能被破坏，导致内存不安全。

**关系**：Type Soundness ⊃ Memory Safety（对于 safe Rust）。

</details>

---

### Q68: Iris 模态断言

Iris 中的 `▷`（later）和 `□`（persistently）模态的含义？

<details>
<summary>答案</summary>

- `▷ P`（Later）："下一 step 后 P 成立"。用于递归定义和逐步推理，保证不动点存在。
- `□ P`（Persistently）："P 不依赖任何独占资源，可被任意复制/共享"。对应 Rust 的共享引用 `&T`。

在 RustBelt 中：

- `&mut T` 对应独占资源 `l ↦ v`
- `&T` 对应持久资源 `□(l ↦ v)`

</details>

---

### Q69: Liveness 属性

如何用线性时序逻辑（LTL）表达 "请求最终会被处理"？

<details>
<summary>答案</summary>

```
□(request → ◇processed)
```

- `□`（Globally）：在所有未来状态
- `request → ◇processed`：如果 request 发生，则最终（`◇`）processed 发生

在 Rust 并发中，这对应：**如果发送了消息，接收者最终会收到**（只要程序不 panic 且通道未关闭）。

</details>

---

### Q70: 参数性 vs 特设多态

参数性多态（Parametric）与特设多态（Ad-hoc）的区别？Rust 分别如何支持？

<details>
<summary>答案</summary>

| 多态类型 | 定义 | Rust 机制 |
|:---|:---|:---|
| 参数性 | 对**所有**类型统一行为 | 泛型 `fn identity<T>(x: T) -> T` |
| 特设 | 对**不同**类型不同行为 | Trait `impl Display for i32` / `for String` |

**参数性定理**：`fn f<T>(x: T) -> T` 必然返回 `x`（或 panic/diverge），因为它对 `T` 一无所知。

**特设**通过 vtable（动态）或单态化（静态）实现多态分发。

</details>

---

### Q71: RustBelt Invariant

RustBelt 中的 "invariant"（不变量）指什么？为什么对 `Vec<T>` 至关重要？

<details>
<summary>答案</summary>

**Invariant**：程序执行期间始终保持为真的断言。

`Vec<T>` 的关键 invariant：

- `len <= cap`
- `ptr` 指向已分配的、大小为 `cap * size_of::<T>()` 的内存块
- 前 `len` 个元素已初始化

`unsafe` 代码（如 `set_len`）可以破坏这些 invariant。RustBelt 用 Iris 的 **invariant 机制** 证明：safe API 的使用者无法破坏这些 invariant，即使存在 `unsafe` 内部实现。

</details>

---

### Q72: Ghost State

分离逻辑中的 Ghost State（幽灵状态）在 Rust 验证中的作用？

<details>
<summary>答案</summary>

**Ghost State**：只在证明中存在、不在运行时存在的辅助状态。

在 Rust 验证中（如 Verus、Iris）：

- 追踪逻辑上的资源所有权（如"这个线程持有锁"）
- 证明并发协议的正确性
- 建立线程间的同步关系

rust,ignore
// Verus 示例：用 ghost 变量证明不变量
proof fn maintain_invariant(x: u32, ghost prev: u32)
    requires x == prev + 1
{
    // ghost 参数只在验证时使用，运行时零开销
}
```

</details>

---

## L5 扩展层：多语言范式对比（4 题）

### Q73: Rust vs Swift

Rust 的所有权与 Swift 的 ARC 有何根本区别？

<details>
<summary>答案</summary>

| 维度 | Rust | Swift |
|:---|:---|:---|
| 机制 | 编译期所有权 + Move | 运行时引用计数（ARC）|
| 开销 | 零运行时开销 | 原子引用计数开销 |
| 循环引用 | 编译期阻止（ borrow checker ）| 需 `weak`/`unowned` 手动解决 |
| 并发安全 | 编译期 `Send/Sync` | 运行时检测（ actors ）|
| 学习曲线 | 陡峭 | 平缓 |

Rust 的 trade-off 是**编译期复杂性换取运行时确定性**。

</details>

---

### Q74: Rust vs C# Span

Rust 的 `&[T]` 与 C# 的 `Span<T>` 的异同？

<details>
<summary>答案</summary>

| 维度 | Rust `&[T]` | C# `Span<T>` |
|:---|:---|:---|
| 安全性 | 编译期（borrow checker）| 运行时检查 + ref struct 限制 |
| 堆栈/堆 | 可指向任意位置 | 可指向堆栈、堆、托管内存 |
| 生命周期 | 编译期追踪 | 受 ref struct 作用域限制 |
| 泛型 | `&[T]` 对任意 `T` | `Span<T>` 对任意 `T` |

C# 的 `Span<T>` 借鉴了 Rust 的切片概念，但安全性依赖运行时和 JIT 优化，而非编译期证明。

</details>

---

### Q75: 零成本抽象

C++ 模板也声称"零成本抽象"，与 Rust 泛型的实现有何不同？

<details>
<summary>答案</summary>

两者都通过**单态化**实现零运行时开销，但：

| 维度 | C++ 模板 | Rust 泛型 |
|:---|:---|:---|
| 类型检查 | 实例化时（可能延迟报错）| 定义时（完整类型检查）|
| 错误信息 | 通常冗长且指向模板内部 | 清晰，指向使用点 |
| 特化 | 完全特化（灵活但复杂）| 有限特化（min_specialization）|
| 约束 | 概念（C++20）| Trait bounds（原生）|
| 编译时间 | 通常更长 | 相对可控 |

Rust 的**早期类型检查**和**Trait 约束**使零成本抽象更易用、更安全。

</details>

---

### Q76: 基于能力的安全

Rust 的所有权系统与"基于能力的安全（Capability-based Security）"有何关联？

<details>
<summary>答案</summary>

**Capability-based Security**：访问权限与对象绑定，而非与主体身份绑定。

Rust 的所有权即一种**能力**：

- 拥有 `File` = 拥有读写该文件的能力
- 拥有 `&mut T` = 拥有修改 `T` 的能力
- `move` = 能力的转移（不可复制的能力）

这与传统 ACL（访问控制列表）不同：Rust 中**没有能力的代码无法访问资源**，无需运行时检查权限。

</details>

---

## L6 扩展层：工程实践与生态（4 题）

### Q77: Cargo Features 解析

`cargo build --features "a b"` 与 `cargo build --features a --features b` 是否等价？

```toml
[features]
default = ["a"]
a = ["dep:tokio"]
b = []
```

<details>
<summary>答案</summary>

**等价**。两种写法都激活 features `a` 和 `b`。

关键规则：

- Features 是**加法性**的：只能启用，不能禁用（除 `--no-default-features`）
- `dep:tokio` 是 feature 重命名语法，表示启用 feature `a` 时自动启用 `tokio` 依赖
- 多个 features 用空格或多次 `--features` 传递效果相同

</details>

---

### Q78: proc-macro2 与 syn

为什么 proc macro crate 通常同时依赖 `proc-macro2` 和 `syn`？

<details>
<summary>答案</summary>

| Crate | 作用 |
|:---|:---|
| `proc-macro2` | 提供与 `proc_macro` 兼容的 TokenStream，但可在 crate 外测试 |
| `syn` | TokenStream 的解析器，将 token 流解析为 AST（`ItemFn`、`Expr` 等）|
| `quote` | 将 Rust 代码模板生成 TokenStream |

**使用流程**：

```text
TokenStream → syn 解析 → 修改 AST → quote 生成 → TokenStream
```

`proc-macro2` 解决了标准库 `proc_macro` 只能在 proc-macro crate 中使用的问题。

</details>

---

### Q79: SemVer 与 API 演进

以下变更属于 SemVer 的哪个级别？

1. 为 trait 添加默认方法
2. 将 `pub fn foo()` 改为 `pub fn foo<T>()`
3. 删除公共模块

<details>
<summary>答案</summary>

| 变更 | SemVer | 说明 |
|:---|:---|:---|
| 添加默认方法 | **Minor** | 不破坏现有代码，新增功能 |
| `foo()` → `foo<T>()` | **Major** | 类型推断可能失败，破坏调用点 |
| 删除公共模块 | **Major** | 直接破坏依赖该模块的代码 |

Rust 的 [API Guidelines](https://rust-lang.github.io/api-guidelines/) 建议对公共 API 谨慎使用 SemVer。

</details>

---

### Q80: rustdoc Doctest

以下文档测试是否能通过？

```rust,ignore
/// ```
/// let x = 5;
/// assert_eq!(x + 1, 6);
/// ```
pub fn foo() {}
```

<details>
<summary>答案</summary>

**能通过**。Rust 的文档测试（doctest）会自动将文档注释中 `` ``` `` 内的代码编译并运行。

**隐藏代码**（不显示在文档中但参与测试）：

```rust,ignore
/// ```
/// # let setup = 5;  // 以 # 开头，隐藏但执行
/// assert_eq!(setup, 5);
/// ```
```

**属性控制**：

- ```` ```ignore ````：不编译
- ```` ```no_run ````：编译但不运行
- ```` ```compile_fail ````：期望编译失败
- ```` ```should_panic ````：期望 panic

</details>

---

> **评分标准**（自我评估）：
>
> - **68-80 题正确**：L1-L6 全部掌握，可深入 L4 形式化细节
> - **54-67 题正确**：L1-L3 扎实，L4-L6 需针对性补强
> - **40-53 题正确**：L1-L2 基本掌握，建议重读对应章节
> - **27-39 题正确**：L1-L2 基础，需系统学习
> - **<27 题正确**：建议从 [`learning_guide.md`](./learning_guide.md) 基础路径重新开始
>
> **深入阅读**：
>
> - L1-L3 完整理论见 [`semantic_space.md`](./semantic_space.md) §2-3
> - L4 形式化背景见 [`../04_formal/`](../04_formal/)
> - L5 对比见 [`../05_comparative/`](../05_comparative/)
> - L6 实践见 [`../06_ecosystem/`](../06_ecosystem/)
