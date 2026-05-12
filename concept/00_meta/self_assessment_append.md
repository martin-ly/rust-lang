
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

```rust
fn longest(x: &str, y: &str) -> &str {
    if x.len() > y.len() { x } else { y }
}
```

<details>
<summary>答案</summary>

**不能编译**。多输入引用时，生命周期省略规则**不适用**，必须显式标注：

```rust
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

```rust
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

```rust
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
```rust
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
```rust
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

```rust
use futures::StreamExt;
while let Some(item) = stream.next().await {
    // 处理 item
}
```

</details>

---

### Q59: Cancel Safety

以下 `select!` 调用是否 cancel-safe？

```rust
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
```rust
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

```rust
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
