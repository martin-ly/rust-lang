# Rust 关键字参考手册

> **版本**: Rust Edition 2024
> **适用范围**: 所有 Rust 开发者
> **内容**: 完整的关键字分类参考，包含严格关键字、保留关键字和特殊标识符

---

## 严格关键字 (Strict Keywords)

严格关键字不能用作变量名、函数名或任何标识符。Rust 在编译时会拒绝将这些关键字作为标识符使用。

### 控制流关键字

控制流关键字用于管理程序的执行顺序，是编程中最基础的部分。

#### `if` / `else`

条件分支控制。`if` 计算布尔表达式，`else` 处理不满足条件的情况。

```rust
let x = 5;
if x > 0 {
    println!("正数");
} else if x < 0 {
    println!("负数");
} else {
    println!("零");
}

// if 是表达式，可以返回值
let abs = if x < 0 { -x } else { x };
```

#### `match`

模式匹配，类似其他语言的 switch，但更强大。支持穷尽性检查。

```rust
let value = 42;
match value {
    0 => println!("零"),
    1..=10 => println!("1-10之间"),
    n if n % 2 == 0 => println!("偶数: {}", n),
    _ => println!("其他"),
}
```

#### `loop`

无限循环，必须用 `break` 退出。可以带标签用于多层循环。

```rust
let mut count = 0;
let result = loop {
    count += 1;
    if count == 10 {
        break count * 2;  // break 可以返回值
    }
};
```

#### `while`

条件循环，在条件为真时持续执行。

```rust
let mut n = 3;
while n != 0 {
    println!("{}!", n);
    n -= 1;
}
```

#### `for`

迭代循环，配合迭代器使用。这是最常用的循环形式。

```rust
for i in 0..5 {
    println!("{}", i);  // 0,1,2,3,4
}

for item in &collection {
    println!("{}", item);
}
```

#### `break`

立即退出循环。可以带返回值（仅在 `loop` 中）或标签。

```rust
'outer: loop {
    loop {
        break 'outer;  // 带标签跳出外层循环
    }
}
```

#### `continue`

跳过当前迭代，进入下一次循环。

```rust
for i in 0..10 {
    if i % 2 == 0 {
        continue;  // 跳过偶数
    }
    println!("奇数: {}", i);
}
```

### 函数相关关键字

#### `fn`

定义函数或方法。支持泛型和多种参数形式。

```rust
fn add(a: i32, b: i32) -> i32 {
    a + b  // 末尾表达式作为返回值（无分号）
}

// 泛型函数
fn identity<T>(x: T) -> T {
    x
}
```

#### `return`

从函数提前返回。Rust 更倾向于使用隐式返回。

```rust
fn divide(a: f64, b: f64) -> Option<f64> {
    if b == 0.0 {
        return None;  // 提前返回
    }
    Some(a / b)  // 隐式返回
}
```

#### `async` / `await`

异步编程关键字（Rust 2018+）。`async` 创建异步块或函数，`await` 等待异步操作完成。

```rust
async fn fetch_data() -> Result<String, Error> {
    let client = reqwest::Client::new();
    let response = client
        .get("https://api.example.com/data")
        .send()
        .await?;  // 等待并传播错误

    response.text().await
}

// 异步闭包 (Rust 2024+)
let closure = async || {
    println!("异步闭包");
};
```

#### `yield`

生成器关键字（Rust 2024+，`gen` 块中使用），产生值并暂停执行。

```rust
#![feature(gen_blocks)]

let gen = gen {
    yield 1;
    yield 2;
    yield 3;
};

for value in gen {
    println!("{}", value);  // 1, 2, 3
}
```

### 类型系统关键字

#### `struct`

定义结构体，可以创建具名结构体、元组结构体和单元结构体。

```rust
struct Point {
    x: f64,
    y: f64,
}

// 元组结构体
struct Color(u8, u8, u8);

// 单元结构体
struct Marker;
```

#### `enum`

定义枚举类型，可以包含不同类型和数量的数据。

```rust
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(u8, u8, u8),
}

// 带泛型的枚举
enum Result<T, E> {
    Ok(T),
    Err(E),
}
```

#### `trait`

定义共享行为的接口，支持默认实现。

```rust
trait Drawable {
    fn draw(&self);

    fn draw_twice(&self) {
        self.draw();
        self.draw();
    }
}
```

#### `impl`

为类型实现方法或 trait。

```rust
impl Point {
    fn new(x: f64, y: f64) -> Self {
        Point { x, y }
    }
}

impl Drawable for Point {
    fn draw(&self) {
        println!("绘制点 ({}, {})", self.x, self.y);
    }
}
```

#### `type`

类型别名，为现有类型创建新名称。

```rust
type Point2D = (f64, f64);
type Callback = fn(i32) -> i32;

// 关联类型（在 trait 中）
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}
```

#### `dyn`

动态分发，用于 trait 对象。运行时确定具体类型。

```rust
fn draw_all(shapes: &[&dyn Drawable]) {
    for shape in shapes {
        shape.draw();
    }
}

let drawable: Box<dyn Drawable> = Box::new(Point::new(0.0, 0.0));
```

### 模块系统关键字

#### `mod`

声明模块。可以是内联模块或引用外部文件。

```rust
// 声明内联模块
mod math {
    pub fn add(a: i32, b: i32) -> i32 {
        a + b
    }
}

// 声明文件模块（对应 math.rs 或 math/mod.rs）
mod math;
```

#### `use`

导入路径到作用域，支持多种导入形式。

```rust
use std::collections::HashMap;
use std::io::{self, Write};  // 导入 io 和 io::Write
use std::fs::*;  // 通配导入
use std::result::Result as StdResult;  // 重命名
```

#### `crate`

引用当前 crate 的根。

```rust
use crate::config::Settings;
pub(crate) fn internal_helper() {}  // crate 可见性
```

#### `super`

引用父模块。

```rust
mod parent {
    pub const VALUE: i32 = 10;

    mod child {
        fn use_parent() {
            println!("{}", super::VALUE);
        }
    }
}
```

#### `extern`

链接外部代码，用于 FFI（外部函数接口）。

```rust
extern "C" {
    fn sqrt(x: f64) -> f64;
}

#[no_mangle]
pub extern "C" fn rust_function() {}
```

#### `pub`

公开可见性修饰符，可以限制可见范围。

```rust
pub struct PublicStruct;
pub(crate) fn crate_visible() {}   // crate 级别
pub(super) fn parent_visible() {}  // 父模块级别
pub(in crate::module) fn limited() {}  // 指定路径
```

### 变量与所有权关键字

#### `let`

绑定变量，支持模式解构。

```rust
let x = 5;
let mut y = 10;
let z: i32 = 20;

// 模式解构
let (a, b) = (1, 2);
let Point { x, y } = point;
```

#### `mut`

可变修饰符，允许修改变量或引用。

```rust
let mut v = vec![1, 2, 3];
v.push(4);

fn push_value(vec: &mut Vec<i32>, val: i32) {
    vec.push(val);
}
```

#### `const`

编译期常量，必须显式标注类型。

```rust
const MAX_SIZE: usize = 100;
const PI: f64 = 3.14159;

const fn square(x: i32) -> i32 {
    x * x
}
```

#### `static`

静态生命周期变量，整个程序运行期间存在。

```rust
static GLOBAL_COUNTER: AtomicUsize = AtomicUsize::new(0);

static mut MUTABLE_STATIC: i32 = 0;  // 需要 unsafe
unsafe {
    MUTABLE_STATIC += 1;
}
```

#### `ref`

通过引用绑定，常用于模式匹配。

```rust
let value = 5;
let ref r = value;  // r 是 &i32

match some_value {
    ref r => println!("引用: {:?}", r),
}
```

### 其他关键字

#### `unsafe`

标记不安全的代码块或项，绕过 Rust 的安全检查。

```rust
unsafe fn dangerous_function() {}

unsafe {
    dangerous_function();
}

unsafe trait Sync {}
unsafe impl Sync for MyType {}
```

#### `as`

类型转换和重命名。

```rust
let x: i32 = 10;
let y: i64 = x as i64;

use std::io::Error as IoError;
```

#### `where`

约束泛型参数，使代码更清晰。

```rust
fn print<T>(value: T)
where
    T: Display + Debug,
{
    println!("{:?}", value);
}
```

#### `move`

强制闭包获取所有权而非借用。

```rust
let data = vec![1, 2, 3];
let closure = move || {
    println!("{:?}", data);  // 获取所有权
};
```

#### `self` / `Self`

- `self`: 方法的第一个参数，表示实例
- `Self`: 当前类型的别名

```rust
impl Rectangle {
    fn area(&self) -> f64 {
        self.width * self.height
    }

    fn square(size: f64) -> Self {
        Self { width: size, height: size }
    }
}
```

#### `in`

用于 `for` 循环和可见性修饰。

```rust
for item in collection { }
pub(in crate::outer) fn limited_visible() {}
```

---

## 保留关键字 (Reserved Keywords)

以下关键字当前未使用，但保留供将来使用，**不能**用作标识符：

| 关键字 | 可能的用途 |
|--------|-----------|
| `abstract` | 抽象类型/方法 |
| `become` | 尾调用优化 |
| `box` | 智能指针构造 |
| `do` | 特定语法块 |
| `final` | 不可覆盖/不可继承 |
| `macro` | 宏定义关键字 |
| `override` | 方法重写 |
| `priv` | 私有可见性 |
| `typeof` | 类型查询 |
| `unsized` | 动态大小类型标记 |
| `virtual` | 虚函数/多态 |
| `try` | 错误处理 |

---

## 特殊标识符 (Special Identifiers)

这些不是严格关键字，但具有特殊含义，建议避免用作标识符。

#### `union`

定义 C 风格联合体（需要 `unsafe`）。

```rust
#[repr(C)]
union IntOrFloat {
    i: i32,
    f: f32,
}

unsafe {
    let u = IntOrFloat { i: 1 };
}
```

#### `'static`

静态生命周期，是最长的生命周期。

```rust
let s: &'static str = "Hello, world!";
fn require_static<T: 'static>(_: T) {}
```

#### `macro_rules!`

定义声明式宏。

```rust
macro_rules! say_hello {
    () => { println!("Hello!"); };
    ($name:expr) => { println!("Hello, {}!", $name); };
}
```

---

## 按类别分类速查

### 🔀 控制流

| 关键字 | 用途 | 示例 |
|--------|------|------|
| `if` / `else` | 条件分支 | `if x > 0 { } else { }` |
| `match` | 模式匹配 | `match val { A => {}, _ => {} }` |
| `loop` | 无限循环 | `loop { break; }` |
| `while` | 条件循环 | `while n > 0 { }` |
| `for` | 迭代循环 | `for x in iter { }` |
| `break` | 退出循环 | `break 'label value;` |
| `continue` | 跳过迭代 | `continue;` |

### ⚙️ 函数

| 关键字 | 用途 | 示例 |
|--------|------|------|
| `fn` | 定义函数 | `fn foo() {}` |
| `return` | 返回值 | `return x;` |
| `async` | 异步函数 | `async fn foo() {}` |
| `await` | 等待异步 | `foo().await` |
| `yield` | 生成器产生值 | `yield value;` |

### 📦 类型

| 关键字 | 用途 | 示例 |
|--------|------|------|
| `struct` | 结构体 | `struct Point { x: f64 }` |
| `enum` | 枚举 | `enum Option<T> { Some(T), None }` |
| `trait` | 接口 | `trait Drawable { fn draw(&self); }` |
| `impl` | 实现 | `impl Trait for Type { }` |
| `type` | 类型别名 | `type ID = u64;` |
| `dyn` | 动态分发 | `Box<dyn Trait>` |

### 📂 模块

| 关键字 | 用途 | 示例 |
|--------|------|------|
| `mod` | 声明模块 | `mod foo;` |
| `use` | 导入 | `use std::io;` |
| `crate` | 当前 crate | `use crate::module;` |
| `super` | 父模块 | `super::parent_fn();` |
| `extern` | 外部链接 | `extern "C" {}` |
| `pub` | 公开 | `pub fn public() {}` |

### 🔧 变量

| 关键字 | 用途 | 示例 |
|--------|------|------|
| `let` | 变量绑定 | `let x = 5;` |
| `mut` | 可变 | `let mut y = 10;` |
| `const` | 常量 | `const PI: f64 = 3.14;` |
| `static` | 静态变量 | `static X: i32 = 0;` |
| `ref` | 引用绑定 | `let ref r = value;` |

### 🔐 其他

| 关键字 | 用途 | 示例 |
|--------|------|------|
| `unsafe` | 不安全代码 | `unsafe { }` |
| `as` | 类型转换 | `x as i64` |
| `where` | 泛型约束 | `where T: Display` |
| `move` | 所有权转移 | `move \|\| {}` |
| `self` / `Self` | 实例/类型 | `fn new() -> Self` |
| `in` | for循环/可见性 | `for x in y` |

---

## 版本说明

| 关键字 | 引入版本 | 说明 |
|--------|----------|------|
| `async` / `await` | Rust 2018 | 异步编程支持 |
| `dyn` | Rust 2018 | 显式 trait 对象 |
| `gen` / `yield` | Rust 2024+ | 生成器（实验性）|
| `async` 闭包 | Rust 2024+ | `async \|\| {}` 语法 |

---

> 💡 **提示**: 编写代码时，现代 IDE 会自动高亮关键字。如果遇到 "expected identifier, found keyword" 错误，说明使用了关键字作为标识符。
