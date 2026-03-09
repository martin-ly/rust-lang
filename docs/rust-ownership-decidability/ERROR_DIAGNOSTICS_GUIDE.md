# Rust 所有权系统 - 错误诊断完全指南

> 系统化的错误诊断方法，从错误信息到解决方案

---

## 🧭 诊断方法论

### 三步诊断法

```
1. 理解错误信息
   └── 读取编译器消息，识别关键术语

2. 分析代码上下文
   └── 定位问题位置，理解所有权流

3. 应用修复模式
   └── 选择合适的解决方案
```

---

## 常见错误分类

### E0382: 使用已移动的值

**错误信息**:

```
error[E0382]: borrow of moved value: `s1`
  --> src/main.rs:5:27
   |
 2 |     let s1 = String::from("hello");
   |         -- move occurs because `s1` has type `String`,
   |            which does not implement the `Copy` trait
 3 |     let s2 = s1;
   |              -- value moved here
 4 |
 5 |     println!("{}", s1);
   |                    ^^ value borrowed here after move
```

**诊断流程**:

```mermaid
graph TD
    A[错误: value borrowed after move] --> B{需要保留原值?}
    B -->|是| C{值是否实现了 Clone?}
    B -->|否| D[无需修改，这是预期行为]

    C -->|是| E[使用 .clone()]
    C -->|否| F{可以使用引用?}

    F -->|是| G[改用借用 &T]
    F -->|否| H[重构代码结构]
```

**解决方案**:

| 场景 | 修复前 | 修复后 |
|:-----|:-------|:-------|
| 需要两个独立副本 | `let s2 = s1;` | `let s2 = s1.clone();` |
| 只需要读取 | `let s2 = s1;` | `let s2 = &s1;` |
| 函数参数 | `fn foo(v: Vec)` | `fn foo(v: &[T])` |
| 返回所有权 | `fn get() -> T` | `fn get() -> &T` |

---

### E0499: 多重可变借用

**错误信息**:

```
error[E0499]: cannot borrow `data` as mutable more than once at a time
  --> src/main.rs:5:14
   |
 4 |     let r1 = &mut data;
   |              --------- first mutable borrow occurs here
 5 |     let r2 = &mut data;
   |              ^^^^^^^^^ second mutable borrow occurs here
 6 |     println!("{}", r1);
   |                    -- first borrow later used here
```

**诊断流程**:

```mermaid
graph TD
    A[错误: multiple mutable borrows] --> B{借用是否可以顺序化?}
    B -->|是| C[使用嵌套作用域]
    B -->|否| D{需要同时访问?}

    D -->|是| E{访问不同部分?}
    E -->|是| F[使用 split_mut]
    E -->|否| G{需要内部可变性?}

    G -->|是| H[使用 RefCell/Mutex]
    G -->|否| I[重构数据结构]
```

**解决方案**:

```rust
// 方案 1: 嵌套作用域
let mut data = vec![1, 2, 3];
{
    let r1 = &mut data;
    r1.push(4);
}  // r1 在这里释放
let r2 = &mut data;  // 可以

// 方案 2: 函数边界
let mut data = vec![1, 2, 3];
process(&mut data);  // 借用结束
process(&mut data);  // 可以再次借用

// 方案 3: 分割借用
let mut data = [1, 2, 3, 4, 5];
let (first, rest) = data.split_at_mut(2);
let (middle, last) = rest.split_at_mut(2);
// first, middle, last 可以同时使用

// 方案 4: 内部可变性
use std::cell::RefCell;
let data = RefCell::new(vec![1, 2, 3]);
data.borrow_mut().push(4);
data.borrow_mut().push(5);  // 可以
```

---

### E0502: 可变与不可变借用冲突

**错误信息**:

```
error[E0502]: cannot borrow `data` as mutable because
               it is also borrowed as immutable
```

**常见场景与修复**:

```rust
// 场景: 遍历并修改
let mut data = vec![1, 2, 3];

// ❌ 错误
for item in &data {
    data.push(*item);  // 错误！
}

// ✅ 修复 1: 收集后处理
let to_add: Vec<i32> = data.iter().copied().collect();
data.extend(to_add);

// ✅ 修复 2: 使用索引
let len = data.len();
for i in 0..len {
    let val = data[i];
    data.push(val);
}

// ✅ 修复 3: 使用 retain (过滤并修改)
data.retain(|&x| {
    // 可以访问并决定是否保留
    x > 0
});
```

---

### E0597: 引用生命周期不够长

**错误信息**:

```
error[E0597]: `s` does not live long enough
  --> src/main.rs:5:13
   |
 4 |     let r = {
   |         let s = String::from("hello");
   |         &s
   |     };
   |       - `s` dropped here while still borrowed
 5 |     println!("{}", r);
   |                 ^ borrowed value does not live long enough
```

**诊断流程**:

```mermaid
graph TD
    A[错误: does not live long enough] --> B{引用是否应该拥有所有权?}
    B -->|是| C[改为 owned type]
    B -->|否| D{生命周期是否可以延长?}

    D -->|是| E[将值移到外部作用域]
    D -->|否| F{是否可以使用 Rc/Arc?}

    F -->|是| G[使用 Rc/Arc 共享所有权]
    F -->|否| H[重构返回值]
```

**解决方案**:

```rust
// 方案 1: 拥有所有权
fn get_string() -> String {
    String::from("hello")
}

// 方案 2: 延长生命周期
fn main() {
    let s = String::from("hello");  // 移到外部
    let r = &s;
    println!("{}", r);
}  // s 在这里释放

// 方案 3: 使用 Rc
use std::rc::Rc;
fn get_shared() -> Rc<String> {
    Rc::new(String::from("hello"))
}

// 方案 4: 'static 生命周期
fn get_static() -> &'static str {
    "hello"  // 字符串字面量是 'static
}
```

---

## 生命周期相关错误

### E0621: 显式生命周期要求

**错误信息**:

```
error[E0621]: explicit lifetime required in the type of `x`
```

**修复模式**:

```rust
// 错误
fn longest(x: &str, y: &str) -> &str {
    if x.len() > y.len() { x } else { y }
}

// 修复
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// 或者使用 elided lifetime (单输入)
fn first(x: &str) -> &str {  // 自动推断
    &x[0..1]
}
```

---

### E0106: 缺少生命周期说明符

**错误信息**:

```
error[E0106]: missing lifetime specifier
```

**修复模式**:

```rust
// 错误
struct Parser {
    text: &str,
}

// 修复
struct Parser<'a> {
    text: &'a str,
}

// 或者拥有所有权
struct Parser {
    text: String,
}
```

---

## 智能指针相关错误

### E0500: 闭包同时需要可变和不可变借用

**错误信息**:

```
error: cannot borrow `x` as mutable because
       it is also borrowed as immutable
```

**修复模式**:

```rust
use std::cell::RefCell;

// 错误
let mut x = vec![1, 2, 3];
let print = || println!("{:?}", x);  // 不可变借用
let add = || x.push(4);               // 可变借用

// 修复
let x = RefCell::new(vec![1, 2, 3]);
let print = || println!("{:?}", *x.borrow());
let add = || x.borrow_mut().push(4);
```

---

### E0716: 临时值生命周期太短

**错误信息**:

```
error[E0716]: temporary value dropped while borrowed
```

**修复模式**:

```rust
// 错误
let r = &String::from("hello");

// 修复 1: 绑定到变量
let s = String::from("hello");
let r = &s;

// 修复 2: 直接拥有
let r = String::from("hello");

// 修复 3: 使用字符串字面量
let r: &'static str = "hello";
```

---

## 并发相关错误

### E0277: 类型未实现 Send

**错误信息**:

```
error[E0277]: `Rc<i32>` cannot be sent between threads safely
```

**修复模式**:

```rust
// 错误
use std::rc::Rc;
use std::thread;

let data = Rc::new(5);
thread::spawn(move || {
    println!("{}", data);
});

// 修复: 使用 Arc
use std::sync::Arc;
let data = Arc::new(5);
thread::spawn(move || {
    println!("{}", data);
});
```

---

### E0596: 无法通过共享引用修改

**错误信息**:

```
error[E0596]: cannot borrow data in a `&` reference as mutable
```

**修复模式**:

```rust
// 错误
let data = Arc::new(vec![1, 2, 3]);
data.push(4);  // 错误！

// 修复
let data = Arc::new(Mutex::new(vec![1, 2, 3]));
data.lock().unwrap().push(4);  // OK
```

---

## 诊断工具

### 使用 rustc 详细输出

```bash
# 详细错误信息
rustc --explain E0382

# 详细诊断
RUST_BACKTRACE=1 cargo run
```

### 使用 Clippy

```bash
# 安装
cargo install clippy

# 运行
cargo clippy

# 所有警告
cargo clippy -- -W clippy::all
```

### 使用 rust-analyzer

- 实时错误提示
- 快速修复建议
- 类型提示

---

## 错误快速参考表

| 错误码 | 描述 | 快速修复 |
|:-------|:-----|:---------|
| E0382 | use of moved value | `.clone()` 或 `&T` |
| E0499 | multiple mutable borrows | 作用域或 `RefCell` |
| E0502 | mutable + immutable | 顺序化借用 |
| E0597 | lifetime too short | 延长作用域或 `Rc/Arc` |
| E0621 | explicit lifetime required | 添加 `'a` 注解 |
| E0106 | missing lifetime specifier | `struct<'a>` |
| E0277 | Send/Sync not satisfied | `Rc` → `Arc` |
| E0596 | cannot borrow as mutable | `Mutex` 或 `RefCell` |
| E0716 | temporary value dropped | 绑定到变量 |

---

## 预防性编程

### 所有权友好的 API 设计

```rust
// 1. 优先使用借用
pub fn process(data: &[u8]) -> Result<(), Error>;

// 2. 使用类型状态防止错误
pub struct Ready;
pub struct Processing;

impl Connection<Ready> {
    pub fn start(self) -> Connection<Processing>;
}

// 3. 使用 RAII
pub struct LockGuard<'a> {
    lock: &'a Lock,
}

impl<'a> Drop for LockGuard<'a> {
    fn drop(&mut self) {
        self.lock.release();
    }
}

// 4. 使用 Newtype 模式
pub struct UserId(u64);
pub struct OrderId(u64);

// 防止混淆
fn find_user(id: UserId) -> User;
fn find_order(id: OrderId) -> Order;
```

---

## 练习

### 练习 1: 诊断并修复

```rust
fn main() {
    let mut data = vec![1, 2, 3];
    let first = &data[0];
    data.push(4);
    println!("{}", first);
}
```

<details>
<summary>解决方案</summary>

```rust
fn main() {
    let mut data = vec![1, 2, 3];
    {
        let first = &data[0];
        println!("{}", first);
    }
    data.push(4);
}
```

</details>

### 练习 2: 诊断并修复

```rust
fn get_ref() -> &String {
    let s = String::from("hello");
    &s
}
```

<details>
<summary>解决方案</summary>

```rust
fn get_owned() -> String {
    String::from("hello")
}

// 或者
fn get_static() -> &'static str {
    "hello"
}
```

</details>

---

## 更多资源

- [交互式学习指南](INTERACTIVE_LEARNING_GUIDE.md)
- [全面 FAQ](COMPREHENSIVE_FAQ.md)
- [案例分析](../case-studies/README.md)
- [Rust 错误索引](https://doc.rust-lang.org/error_codes/error-index.html)

---

*本指南持续更新，欢迎贡献*
