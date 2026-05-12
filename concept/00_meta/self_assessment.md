# Rust 知识体系自测题库（Self-Assessment）

> **定位**：每个层级配套的自测题，用于验证知识掌握程度。答案和解析附在每题之后（可折叠）。
> **使用方式**：先做题，再对答案。建议配合 [`learning_guide.md`](./learning_guide.md) 使用。

---

## L1 基础层：所有权与类型系统（8 题）

### Q1: Move vs Copy

以下代码能否编译？如果不能，为什么？

```rust
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

```rust
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

```rust
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

```rust
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

```rust
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

```rust
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

```rust
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
