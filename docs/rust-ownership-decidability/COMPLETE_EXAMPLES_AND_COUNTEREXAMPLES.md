# Rust 所有权系统 - 完整示例与反例集

**目标**: 通过正例、反例和边界案例，全面理解 Rust 所有权系统

---

## 目录

- [Rust 所有权系统 - 完整示例与反例集](#rust-所有权系统---完整示例与反例集)
  - [目录](#目录)
  - [1. 基础所有权示例](#1-基础所有权示例)
    - [1.1 移动语义](#11-移动语义)
    - [1.2 Copy trait](#12-copy-trait)
    - [1.3 Drop trait](#13-drop-trait)
  - [2. 借用系统示例](#2-借用系统示例)
    - [2.1 不可变借用](#21-不可变借用)
    - [2.2 可变借用](#22-可变借用)
    - [2.3 混合借用规则](#23-混合借用规则)
  - [3. 生命周期示例](#3-生命周期示例)
    - [3.1 显式生命周期](#31-显式生命周期)
    - [3.2 生命周期省略](#32-生命周期省略)
    - [3.3 'static 生命周期](#33-static-生命周期)
  - [4. 复合类型示例](#4-复合类型示例)
    - [4.1 结构体与所有权](#41-结构体与所有权)
    - [4.2 枚举与所有权](#42-枚举与所有权)
  - [5. 高级模式示例](#5-高级模式示例)
    - [5.1 智能指针](#51-智能指针)
    - [5.2 闭包与所有权](#52-闭包与所有权)
  - [6. 反例合集](#6-反例合集)
    - [6.1 所有权错误](#61-所有权错误)
    - [6.2 借用错误](#62-借用错误)
    - [6.3 生命周期错误](#63-生命周期错误)
  - [7. 边界案例分析](#7-边界案例分析)
    - [7.1 自引用结构体](#71-自引用结构体)
    - [7.2 协变与逆变](#72-协变与逆变)
    - [7.3 内部可变性模式](#73-内部可变性模式)
  - [8. 常见错误诊断](#8-常见错误诊断)
    - [8.1 错误诊断流程图](#81-错误诊断流程图)
    - [8.2 错误信息速查表](#82-错误信息速查表)
  - [总结](#总结)

---

## 1. 基础所有权示例

### 1.1 移动语义

```rust
// ===== 示例 1.1.1: 基本移动 =====
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 的所有权移动到 s2

    println!("{}", s2);  // ✅ 正常
    // println!("{}", s1);  // ❌ 错误: value borrowed here after move
}

// ===== 示例 1.1.2: 函数参数移动 =====
fn takes_ownership(s: String) {
    println!("{}", s);
} // s 在这里被释放

fn main() {
    let s = String::from("hello");
    takes_ownership(s);  // s 的所有权移动到函数
    // println!("{}", s);  // ❌ 错误: s 已被移动
}

// ===== 示例 1.1.3: 返回值移动 =====
fn gives_ownership() -> String {
    String::from("yours")
}

fn main() {
    let s = gives_ownership();  // 获得返回值的所有权
    println!("{}", s);  // ✅ 正常
}

// ===== 示例 1.1.4: 多重移动链 =====
fn main() {
    let s = String::from("hello");
    let s = move_through(s);  // 第一次移动
    let s = move_through(s);  // 第二次移动
    println!("{}", s);  // ✅ 正常
}

fn move_through(s: String) -> String {
    s  // 返回所有权
}
```

### 1.2 Copy trait

```rust
// ===== 示例 1.2.1: 基本类型的 Copy =====
fn main() {
    let x = 5;
    let y = x;  // x 被复制，不是移动

    println!("x = {}, y = {}", x, y);  // ✅ 两者都可用
}

// ===== 示例 1.2.2: 元组的 Copy =====
fn main() {
    let t1 = (1, 2, 3);  // (i32, i32, i32) 实现 Copy
    let t2 = t1;

    println!("{:?} {:?}", t1, t2);  // ✅ 两者都可用
}

// ===== 示例 1.2.3: 包含引用的元组 (不实现 Copy) =====
fn main() {
    let s = String::from("hello");
    let t1 = (s, 1);  // (String, i32) 不实现 Copy
    let t2 = t1;

    // println!("{:?}", t1);  // ❌ 错误: t1 已被移动
    println!("{:?}", t2);  // ✅ 正常
}

// ===== 示例 1.2.4: 手动实现 Copy =====
#[derive(Clone, Copy)]
struct Point {
    x: i32,
    y: i32,
}

fn main() {
    let p1 = Point { x: 1, y: 2 };
    let p2 = p1;  // 复制，不是移动

    println!("{:?} {:?}", p1, p2);  // ✅ 两者都可用
}
```

### 1.3 Drop trait

```rust
// ===== 示例 1.3.1: 自动 Drop =====
struct CustomDrop {
    name: String,
}

impl Drop for CustomDrop {
    fn drop(&mut self) {
        println!("Dropping CustomDrop: {}", self.name);
    }
}

fn main() {
    let c = CustomDrop { name: String::from("my_resource") };
    // c 在这里离开作用域，自动调用 drop
} // 输出: Dropping CustomDrop: my_resource

// ===== 示例 1.3.2: 提前 Drop =====
fn main() {
    let c = CustomDrop { name: String::from("resource") };

    drop(c);  // 显式提前释放
    // c 从这里开始不可用

    println!("After drop");  // ✅ 正常
    // println!("{}", c.name);  // ❌ 错误: use of moved value
}

// ===== 示例 1.3.3: 转移后不再 Drop =====
fn main() {
    let c = CustomDrop { name: String::from("resource") };
    take_ownership(c);  // c 被移动
    // main 中不再调用 c 的 drop
}

fn take_ownership(c: CustomDrop) {
    // c 在这里离开作用域时调用 drop
}
```

---

## 2. 借用系统示例

### 2.1 不可变借用

```rust
// ===== 示例 2.1.1: 基本不可变借用 =====
fn main() {
    let x = 5;
    let r = &x;  // 不可变借用

    println!("r = {}", r);  // ✅ 读取
    // *r = 10;  // ❌ 错误: cannot assign to immutable borrowed content
}

// ===== 示例 2.1.2: 多个不可变借用 =====
fn main() {
    let x = 5;
    let r1 = &x;
    let r2 = &x;
    let r3 = &x;

    println!("{} {} {}", r1, r2, r3);  // ✅ 多个读者同时存在
}

// ===== 示例 2.1.3: 函数中的借用 =====
fn calculate_length(s: &String) -> usize {
    s.len()  // 读取，不获取所有权
}

fn main() {
    let s = String::from("hello");
    let len = calculate_length(&s);  // 借用

    println!("{} 的长度是 {}", s, len);  // ✅ s 仍然可用
}
```

### 2.2 可变借用

```rust
// ===== 示例 2.2.1: 基本可变借用 =====
fn main() {
    let mut x = 5;
    let r = &mut x;  // 可变借用

    *r = 10;  // ✅ 通过引用修改
    println!("r = {}", r);  // ✅ 读取
}

// ===== 示例 2.2.2: 独占性 =====
fn main() {
    let mut x = 5;
    let r1 = &mut x;
    // let r2 = &mut x;  // ❌ 错误: cannot borrow as mutable more than once

    println!("{}", r1);
}

// ===== 示例 2.2.3: 可变借用序列 =====
fn main() {
    let mut x = 5;

    {
        let r1 = &mut x;
        *r1 = 10;
    }  // r1 在这里结束

    let r2 = &mut x;  // ✅ 可以，r1 已经失效
    *r2 = 20;
}

// ===== 示例 2.2.4: 函数返回可变借用 =====
fn first_mut(nums: &mut [i32]) -> &mut i32 {
    &mut nums[0]
}

fn main() {
    let mut v = vec![1, 2, 3];
    let first = first_mut(&mut v);
    *first = 100;

    println!("{:?}", v);  // ✅ [100, 2, 3]
}
```

### 2.3 混合借用规则

```rust
// ===== 示例 2.3.1: 不能同时有 & 和 &mut =====
fn main() {
    let mut x = 5;
    let r1 = &x;  // 不可变借用
    // let r2 = &mut x;  // ❌ 错误: cannot borrow as mutable

    println!("{}", r1);
}

// ===== 示例 2.3.2: 生命周期不重叠时 OK =====
fn main() {
    let mut x = 5;

    let r1 = &x;
    println!("{}", r1);  // r1 最后一次使用

    let r2 = &mut x;  // ✅ r1 已不再使用
    println!("{}", r2);
}

// ===== 示例 2.3.3: NLL (Non-Lexical Lifetimes) =====
fn main() {
    let mut x = 5;
    let r = &x;

    if *r > 0 {
        println!("正数");
    }  // r 在这里之后不再使用

    let m = &mut x;  // ✅ 可以，因为 r 不再使用
    *m = 10;
}
```

---

## 3. 生命周期示例

### 3.1 显式生命周期

```rust
// ===== 示例 3.1.1: 显式标注 =====
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

fn main() {
    let s1 = String::from("hello");
    let s2 = String::from("world");

    let result = longest(&s1, &s2);
    println!("最长的字符串是 {}", result);
}

// ===== 示例 3.1.2: 不同生命周期 =====
fn main() {
    let s1 = String::from("long string is long");
    {
        let s2 = String::from("xyz");
        let result = longest(&s1, &s2);
        println!("{}", result);  // ✅ 在 s2 的作用域内使用
    }  // s2 结束，result 不再有效
}

// ===== 示例 3.1.3: 结构体生命周期 =====
struct ImportantExcerpt<'a> {
    part: &'a str,
}

impl<'a> ImportantExcerpt<'a> {
    fn level(&self) -> i32 {
        3
    }

    fn announce_and_return_part(&self, announcement: &str) -> &str {
        println!("注意！{}", announcement);
        self.part
    }
}

fn main() {
    let novel = String::from("Call me Ishmael. Some years ago...");
    let first_sentence = novel.split('.').next().unwrap();
    let i = ImportantExcerpt { part: first_sentence };

    println!("{}", i.part);
}
```

### 3.2 生命周期省略

```rust
// ===== 示例 3.2.1: 规则 1 - 输入生命周期 =====
fn foo(x: &i32) {  // 省略: fn foo<'a>(x: &'a i32)
    // x 获得生命周期 'a
}

// ===== 示例 3.2.2: 规则 2 - 单一输入 =====
fn foo(x: &i32) -> &i32 {  // 省略: fn foo<'a>(x: &'a i32) -> &'a i32
    x
}

// ===== 示例 3.2.3: 规则 3 - 多个输入需要显式 =====
// fn longest(x: &str, y: &str) -> &str {  // ❌ 无法推断
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {  // ✅ 需要显式
    if x.len() > y.len() { x } else { y }
}

// ===== 示例 3.2.4: 方法中的 &self =====
impl MyStruct {
    fn get_ref(&self) -> &Data {  // 省略: fn get_ref<'a>(&'a self) -> &'a Data
        &self.data
    }
}
```

### 3.3 'static 生命周期

```rust
// ===== 示例 3.3.1: 字符串字面量 =====
fn main() {
    let s: &'static str = "我有 'static 生命周期";
    // 字符串字面量存储在二进制中，程序整个运行期间有效
}

// ===== 示例 3.3.2: 常量 =====
const CONST_STRING: &'static str = "常量字符串";

// ===== 示例 3.3.3: 与泛型结合 =====
fn return_static() -> &'static str {
    "总是返回 'static 字符串"
}

// ===== 示例 3.3.4: 存储 'static 引用 =====
struct Config {
    name: &'static str,  // 只接受 'static 字符串
}

fn main() {
    let config = Config { name: "应用配置" };
    println!("{}", config.name);
}
```

---

## 4. 复合类型示例

### 4.1 结构体与所有权

```rust
// ===== 示例 4.1.1: 所有权结构体 =====
struct User {
    username: String,
    email: String,
    sign_in_count: u64,
    active: bool,
}

fn main() {
    let user1 = User {
        username: String::from("alice"),
        email: String::from("alice@example.com"),
        sign_in_count: 1,
        active: true,
    };

    let user2 = user1;  // 所有字段被移动
    // println!("{}", user1.username);  // ❌ 错误: user1 已被移动
}

// ===== 示例 4.1.2: 结构体更新语法 =====
fn main() {
    let user1 = User {
        username: String::from("alice"),
        email: String::from("alice@example.com"),
        sign_in_count: 1,
        active: true,
    };

    let user2 = User {
        email: String::from("new@example.com"),
        ..user1  // 其余字段从 user1 移动
    };

    // println!("{}", user1.username);  // ❌ 错误: username 已被移动
    println!("{}", user1.sign_in_count);  // ✅ Copy 类型没有被移动
}

// ===== 示例 4.1.3: 引用字段的结构体 =====
struct UserRef<'a> {
    username: &'a str,
    email: &'a str,
}

fn main() {
    let username = String::from("alice");
    let email = String::from("alice@example.com");

    let user = UserRef {
        username: &username,
        email: &email,
    };

    println!("{} {}", user.username, user.email);
}  // user 先失效，然后 username 和 email 失效
```

### 4.2 枚举与所有权

```rust
// ===== 示例 4.2.1: 拥有所有权的枚举 =====
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(i32, i32, i32),
}

fn main() {
    let m1 = Message::Write(String::from("hello"));
    let m2 = m1;  // 所有权转移
    // println!("{:?}", m1);  // ❌ 错误
}

// ===== 示例 4.2.2: Option 和所有权 =====
fn main() {
    let some_string = Some(String::from("hello"));

    match some_string {
        Some(s) => println!("{}", s),  // s 获得所有权
        None => println!("无值"),
    }

    // println!("{:?}", some_string);  // ❌ 错误: 已被移动
}

// ===== 示例 4.2.3: 使用 as_ref 避免移动 =====
fn main() {
    let some_string = Some(String::from("hello"));

    match some_string.as_ref() {
        Some(s) => println!("{}", s),  // s 是 &String
        None => println!("无值"),
    }

    println!("{:?}", some_string);  // ✅ 正常，没有被移动
}
```

---

## 5. 高级模式示例

### 5.1 智能指针

```rust
// ===== 示例 5.1.1: Box<T> =====
fn main() {
    let b = Box::new(5);  // 在堆上分配
    println!("{}", b);     // ✅ 自动解引用
}  // b 被释放，堆内存被释放

// ===== 示例 5.1.2: Rc<T> (引用计数) =====
use std::rc::Rc;

fn main() {
    let data = Rc::new(String::from("共享数据"));

    let data2 = Rc::clone(&data);  // 增加引用计数
    let data3 = Rc::clone(&data);  // 增加引用计数

    println!("计数: {}", Rc::strong_count(&data));  // 3
    println!("{} {} {}", data, data2, data3);
}  // 所有引用结束时，内存释放

// ===== 示例 5.1.3: RefCell<T> (内部可变性) =====
use std::cell::RefCell;

fn main() {
    let data = RefCell::new(5);

    {
        let mut ref_mut = data.borrow_mut();
        *ref_mut = 10;
    }  // 可变借用结束

    println!("{}", data.borrow());  // 输出: 10

    // let r1 = data.borrow_mut();
    // let r2 = data.borrow_mut();  // ❌ 运行时panic，不是编译错误
}
```

### 5.2 闭包与所有权

```rust
// ===== 示例 5.2.1: 闭包捕获环境 =====
fn main() {
    let x = 5;
    let equal_to_x = |z| z == x;  // 不可变借用 x

    println!("{}", x);  // ✅ 可以，只是借用
    println!("{}", equal_to_x(5));
}

// ===== 示例 5.2.2: 强制移动捕获 =====
fn main() {
    let x = String::from("hello");

    let consume_x = move || {
        println!("{}", x);  // x 被移动到闭包
    };

    // println!("{}", x);  // ❌ 错误: x 已被移动
    consume_x();
}

// ===== 示例 5.2.3: Fn, FnMut, FnOnce =====
fn call_with_closure<F>(f: F)
where
    F: Fn(),  // 可以多次调用，不修改环境
{
    f();
    f();
}

fn main() {
    let x = 5;
    let closure = || println!("{}", x);  // 实现 Fn

    call_with_closure(closure);
}
```

---

## 6. 反例合集

### 6.1 所有权错误

```rust
// ===== 反例 6.1.1: 使用已移动的值 =====
fn main() {
    let s = String::from("hello");
    let s2 = s;
    println!("{}", s);  // ❌ error[E0382]: borrow of moved value: `s`
}

// ===== 反例 6.1.2: 部分移动 =====
struct Person {
    name: String,
    age: u32,
}

fn main() {
    let p = Person {
        name: String::from("Alice"),
        age: 30,
    };

    let name = p.name;  // name 字段被移动
    // println!("{} {}", p.name, p.age);  // ❌ p.name 已被移动
    println!("{}", p.age);  // ✅ age 是 Copy 类型
}

// ===== 反例 6.1.3: 在循环中移动 =====
fn main() {
    let v = vec![String::from("a"), String::from("b")];

    for s in v {  // v 被移动
        println!("{}", s);
    }

    // println!("{:?}", v);  // ❌ v 已被移动
}
```

### 6.2 借用错误

```rust
// ===== 反例 6.2.1: 同时有 & 和 &mut =====
fn main() {
    let mut x = 5;
    let r1 = &x;
    let r2 = &mut x;  // ❌ error[E0502]: cannot borrow as mutable
    println!("{} {}", r1, r2);
}

// ===== 反例 6.2.2: 多个可变借用 =====
fn main() {
    let mut x = 5;
    let r1 = &mut x;
    let r2 = &mut x;  // ❌ error[E0499]: cannot borrow as mutable more than once
    println!("{} {}", r1, r2);
}

// ===== 反例 6.2.3: 悬垂引用 =====
fn dangling() -> &String {
    let s = String::from("hello");
    &s  // ❌ error[E0106]: missing lifetime specifier
}  // s 被释放，返回的引用无效

// ===== 反例 6.2.4: 生命周期不够长 =====
fn main() {
    let r;
    {
        let x = 5;
        r = &x;  // ❌ error[E0597]: `x` does not live long enough
    }  // x 在这里结束
    println!("{}", r);  // r 引用无效的 x
}
```

### 6.3 生命周期错误

```rust
// ===== 反例 6.3.1: 返回引用不明确 =====
fn longest(x: &str, y: &str) -> &str {  // ❌ 需要显式生命周期
    if x.len() > y.len() { x } else { y }
}

// ===== 反例 6.3.2: 结构体字段引用比结构体活得短 =====
struct Dangling<'a> {
    s: &'a String,
}

fn make_dangling() -> Dangling<'static> {
    let s = String::from("hello");
    Dangling { s: &s }  // ❌ s 在函数结束时被释放
}

// ===== 反例 6.3.3: 方法生命周期不匹配 =====
impl<'a> MyStruct<'a> {
    fn get_ref(&self) -> &'static str {  // ❌ 可能不匹配
        self.s  // self.s 可能不是 'static
    }
}
```

---

## 7. 边界案例分析

### 7.1 自引用结构体

```rust
// ===== 反例 7.1.1: 尝试创建自引用 =====
struct SelfReference {
    data: String,
    // ptr: &str,  // 如果指向 data，移动结构体后会失效
}

// ===== 解决方案: 使用索引而不是引用 =====
struct SelfReferenceSafe {
    data: String,
    start: usize,  // data[start..end]
    end: usize,
}

// ===== 解决方案: 使用 Pin =====
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfReferential {
    data: String,
    ptr: *const String,
    _pin: PhantomPinned,
}

impl SelfReferential {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::pin(Self {
            data,
            ptr: std::ptr::null(),
            _pin: PhantomPinned,
        });
        let ptr = &boxed.data as *const String;
        unsafe {
            let mut_ref: Pin<&mut Self> = Pin::as_mut(&mut boxed);
            Pin::get_unchecked_mut(mut_ref).ptr = ptr;
        }
        boxed
    }
}
```

### 7.2 协变与逆变

```rust
// ===== 示例 7.2.1: &T 是协变的 =====
fn get_static_ref() -> &'static str {
    "static string"
}

fn use_ref<'a>(s: &'a str) {
    println!("{}", s);
}

fn main() {
    let s: &'static str = get_static_ref();
    use_ref(s);  // ✅ 'static <: 'a
}

// ===== 示例 7.2.2: &mut T 是不变的 =====
fn main() {
    let mut s = String::from("hello");
    let r: &mut String = &mut s;
    // 不能将 &mut String 转为 &mut str
}

// ===== 示例 7.2.3: Box<T> 是协变的 =====
fn box_example() {
    let b: Box<&'static str> = Box::new("static");
    let _: Box<&str> = b;  // ✅ 协变
}
```

### 7.3 内部可变性模式

```rust
// ===== 示例 7.3.1: Cell<T> (只能 Copy 类型) =====
use std::cell::Cell;

fn main() {
    let cell = Cell::new(5);
    cell.set(10);  // ✅ 不需要 &mut
    println!("{}", cell.get());
}

// ===== 示例 7.3.2: RefCell<T> (运行时检查) =====
use std::cell::RefCell;

fn main() {
    let ref_cell = RefCell::new(String::from("hello"));

    {
        let mut s = ref_cell.borrow_mut();
        s.push_str(" world");
    }

    // 以下代码会在运行时 panic
    // let r1 = ref_cell.borrow_mut();
    // let r2 = ref_cell.borrow_mut();  // panic!
}

// ===== 示例 7.3.3: Mutex<T> (线程安全) =====
use std::sync::Mutex;

fn main() {
    let mutex = Mutex::new(0);

    {
        let mut num = mutex.lock().unwrap();
        *num = 5;
    }  // 锁在这里释放

    println!("{:?}", mutex);
}
```

---

## 8. 常见错误诊断

### 8.1 错误诊断流程图

```text
遇到所有权/借用错误
        │
        ▼
错误是否提到 "moved value"？
        │
   ┌────┴────┐
  是         否 → 检查借用规则
   │
   ▼
是否需要保留原变量？
   │
┌──┴──┐
是     否
│      │
▼      ▼
使用 .clone()  重构代码
或使用引用     转移所有权

─────────────────────────────

遇到生命周期错误
        │
        ▼
是否缺少生命周期标注？
        │
   ┌────┴────┐
  是         否 → 检查引用有效性
   │
   ▼
函数返回引用？
   │
┌──┴──┐
是     否
│      │
▼      ▼
显式标注  检查是否返回局部变量引用
<'a>     或引用比被引用者活得长
```

### 8.2 错误信息速查表

| 错误信息 | 含义 | 解决方案 |
|---------|------|---------|
| `use of moved value` | 值已被移动 | 使用 .clone() 或引用 |
| `cannot borrow as mutable` | 违反借用规则 | 检查是否已有借用 |
| `cannot borrow as mutable more than once` | 多个可变借用 | 使用不同作用域 |
| `value does not live long enough` | 生命周期问题 | 确保引用有效 |
| `missing lifetime specifier` | 需要生命周期标注 | 添加 <'a> |
| `borrowed value does not live long enough` | 被引用者活得太短 | 延长被引用者生命周期 |

---

## 总结

本文档提供了：

- ✅ 8大类别的完整示例
- ✅ 详细的反例分析
- ✅ 边界案例研究
- ✅ 错误诊断流程

**建议**: 通过实践这些示例来加深理解。
