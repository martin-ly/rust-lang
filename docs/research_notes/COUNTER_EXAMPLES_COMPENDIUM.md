# 反例汇编 (Counter-Examples Compendium)

> **创建日期**: 2026-02-23
> **目标**: 通过反例理解Rust安全机制的边界
> **理念**: "通过理解什么会失败，来理解什么能成功"

---

## 如何使用本文档

```text
学习建议:
1. 先阅读错误代码
2. 尝试理解为什么失败
3. 查看编译器错误信息
4. 阅读解释
5. 查看修复方案
6. 理解背后的原理
```

---

## 一、所有权反例

### 反例 1.1: 使用已移动的值

**错误代码**:

```rust
fn main() {
    let x = String::from("hello");
    let y = x;           // 所有权从x转移到y
    println!("{}", x);   // 错误: 使用已移动的x
}
```

**编译器错误**:

```
error[E0382]: borrow of moved value: `x`
 --> src/main.rs:4:20
  |
2 |     let x = String::from("hello");
  |         - move occurs because `x` has type `String`, which does not implement the `Copy` trait
3 |     let y = x;
  |             - value moved here
4 |     println!("{}", x);
  |                    ^ value borrowed here after move
```

**解释**:

- `String`不实现`Copy` trait，赋值时转移所有权
- 第3行后，`x`不再拥有字符串
- 第4行尝试使用`x`，但`x`已无效

**修复方案**:

```rust
// 方案1: 使用clone
let y = x.clone();
println!("{}", x);  // OK

// 方案2: 借用
let y = &x;
println!("{}", x);  // OK

// 方案3: 直接使用y
println!("{}", y);  // OK
```

**形式化原理**:

```
Move(x, y, v) 后:
- Ω(y) = Owned, Γ(y) = v
- Ω(x) = Moved, Γ(x) = None
- 使用Moved状态的变量 = 错误
```

---

### 反例 1.2: 部分移动后的使用

**错误代码**:

```rust
struct Person {
    name: String,
    age: u32,
}

fn main() {
    let p = Person {
        name: String::from("Alice"),
        age: 30,
    };

    let name = p.name;   // 移动了name字段
    println!("{}", p.age);  // OK
    println!("{}", p.name); // 错误: 部分移动
}
```

**编译器错误**:

```
error[E0382]: borrow of partially moved value: `p`
 --> src/main.rs:12:20
  |
9 |     let name = p.name;
  |                ------ value moved here
...
12 |     println!("{}", p.name);
  |                    ^ value borrowed here after partial move
```

**解释**:

- 结构体的单个字段可以被移动
- 移动后，整个结构体部分无效
- 未移动的字段仍可使用

**修复方案**:

```rust
// 方案1: 借用字段
let name = &p.name;

// 方案2: 使用clone
let name = p.name.clone();

// 方案3: 解构整个结构体
let Person { name, age } = p;
// 之后不能再用p
```

---

## 二、借用反例

### 反例 2.1: 可变借用与不可变借用冲突

**错误代码**:

```rust
fn main() {
    let mut x = 5;
    let r1 = &x;        // 不可变借用
    let r2 = &mut x;    // 错误: 不能同时有可变借用
    println!("{}", r1);
}
```

**编译器错误**:

```
error[E0502]: cannot borrow `x` as mutable because it is also borrowed as immutable
 --> src/main.rs:4:14
  |
3 |     let r1 = &x;
  |              -- immutable borrow occurs here
4 |     let r2 = &mut x;
  |              ^^^^^^^ mutable borrow occurs here
5 |     println!("{}", r1);
  |                  -- immutable borrow later used here
```

**解释**:

- 规则: 要么多个不可变借用，要么一个可变借用
- `r1`仍然存在（被第5行使用），所以不能创建`r2`

**修复方案**:

```rust
// 方案1: 缩小r1的作用域
{
    let r1 = &x;
    println!("{}", r1);
} // r1在这里结束
let r2 = &mut x;  // OK

// 方案2: 只使用可变借用
let r2 = &mut x;
*r2 += 1;
```

**形式化原理**:

```
borrowed_imm(x, r₁, v) → cannot borrowed_mut(x, r₂, v)
until r₁ is dropped
```

---

### 反例 2.2: 多个可变借用

**错误代码**:

```rust
fn main() {
    let mut x = 5;
    let r1 = &mut x;
    let r2 = &mut x;    // 错误: 不能有两个可变借用
    *r1 = 10;
    *r2 = 20;
}
```

**编译器错误**:

```
error[E0499]: cannot borrow `x` as mutable more than once at a time
 --> src/main.rs:4:14
  |
3 |     let r1 = &mut x;
  |              -------- first mutable borrow occurs here
4 |     let r2 = &mut x;
  |              ^^^^^^^^ second mutable borrow occurs here
5 |     *r1 = 10;
  |     -------- first borrow later used here
```

**解释**:

- 可变借用具有排他性
- 同时存在两个可变借用会导致数据竞争

**修复方案**:

```rust
// 顺序使用
let r1 = &mut x;
*r1 = 10;
drop(r1);  // 显式结束借用

let r2 = &mut x;
*r2 = 20;
```

---

### 反例 2.3: 悬垂引用

**错误代码**:

```rust
fn dangling() -> &String {
    let s = String::from("hello");
    &s  // 错误: s将在函数结束时被释放
}
```

**编译器错误**:

```
error[E0106]: missing lifetime specifier
 --> src/main.rs:1:17
  |
1 | fn dangling() -> &String {
  |                 ^ expected named lifetime parameter
  |
  = help: this function's return type contains a borrowed value, but there is no value for it to be borrowed from
```

**解释**:

- `s`在栈上分配，函数结束时被释放
- 返回的引用指向已释放内存
- Rust通过生命周期检查防止悬垂引用

**修复方案**:

```rust
// 方案1: 返回所有权
fn not_dangling() -> String {
    let s = String::from("hello");
    s  // 转移所有权
}

// 方案2: 传入引用
fn not_dangling2(s: &String) -> &String {
    s  // 返回传入的引用
}
```

**形式化原理**:

```
lifetime(&s) ⊆ lifetime(s)
函数结束 → s被释放 → &s无效
```

---

## 三、生命周期反例

### 反例 3.1: 返回局部变量的引用

**错误代码**:

```rust
fn longest(x: &str, y: &str) -> &str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

**编译器错误**:

```
error[E0106]: missing lifetime specifier
 --> src/main.rs:1:33
  |
1 | fn longest(x: &str, y: &str) -> &str {
  |            -----     -----     ^ expected named lifetime parameter
  |
  = help: this function's return type contains a borrowed value with an elided lifetime, but the lifetime cannot be derived from the arguments
```

**解释**:

- 返回的引用可能是`x`或`y`
- 编译器不知道返回引用的生命周期与哪个参数关联
- 需要显式生命周期标注

**修复方案**:

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

**理解**:

```
'a 表示: 返回的引用至少和x、y中较短的生命周期一样长
```

---

## 四、Send/Sync反例

### 反例 4.1: Rc跨线程

**错误代码**:

```rust
use std::rc::Rc;
use std::thread;

fn main() {
    let data = Rc::new(5);

    thread::spawn(move || {
        println!("{}", data);
    });
}
```

**编译器错误**:

```
error[E0277]: `Rc<i32>` cannot be sent between threads safely
 --> src/main.rs:6:5
  |
6 |     thread::spawn(move || {
  |     ^^^^^^^^^^^^^ `Rc<i32>` cannot be sent between threads safely
  |
  = help: the trait `Send` is not implemented for `Rc<i32>`
```

**解释**:

- `Rc`使用非原子引用计数
- 跨线程使用会导致数据竞争（计数更新）
- 使用`Arc`（原子引用计数）代替

**修复方案**:

```rust
use std::sync::Arc;

let data = Arc::new(5);
thread::spawn(move || {
    println!("{}", data);  // OK
});
```

**形式化原理**:

```
Rc<T>: !Send because ref_count++ is not atomic
Arc<T>: Send because AtomicUsize operations are thread-safe
```

---

### 反例 4.2: RefCell跨线程

**错误代码**:

```rust
use std::cell::RefCell;
use std::thread;

fn main() {
    let data = RefCell::new(5);

    thread::spawn(move || {
        *data.borrow_mut() = 10;
    });
}
```

**编译器错误**:

```
error[E0277]: `RefCell<i32>` cannot be sent between threads safely
  --> src/main.rs:6:5
   |
6 |     thread::spawn(move || {
   |     ^^^^^^^^^^^^^ `RefCell<i32>` cannot be sent between threads safely
   |
   = help: the trait `Send` is not implemented for `RefCell<i32>`
```

**解释**:

- `RefCell`在运行时检查借用规则
- 运行时检查不是线程安全的
- 使用`Mutex`或`RwLock`代替

**修复方案**:

```rust
use std::sync::Mutex;

let data = Mutex::new(5);
thread::spawn(move || {
    *data.lock().unwrap() = 10;  // OK
});
```

---

## 五、异步反例

### 反例 5.1: 跨await持有锁

**错误代码**:

```rust
async fn bad() {
    let mutex = Mutex::new(0);
    let guard = mutex.lock().unwrap();

    some_async_fn().await;  // 危险!

    // 使用 guard
}
```

**警告**: 这会导致死锁！

**解释**:

- `.await`可能让出线程执行其他任务
- 如果其他任务需要同一锁，会导致死锁
- 使用`tokio::sync::Mutex`代替

**修复方案**:

```rust
use tokio::sync::Mutex;  // 异步版本的Mutex

async fn good() {
    let mutex = Mutex::new(0);

    {
        let guard = mutex.lock().await;
        // 使用 guard
    }  // 锁在这里释放

    some_async_fn().await;  // OK
}
```

---

## 六、设计模式反例

### 反例 6.1: 尝试实现经典单例

**错误代码**:

```rust
static mut INSTANCE: Option<Singleton> = None;

fn get_instance() -> &'static Singleton {
    unsafe {
        if INSTANCE.is_none() {
            INSTANCE = Some(Singleton::new());
        }
        INSTANCE.as_ref().unwrap()
    }
}
```

**问题**:

- 需要`unsafe`
- 线程不安全
- 没有生命周期管理

**Rust惯用法**:

```rust
use std::sync::OnceLock;

static INSTANCE: OnceLock<Singleton> = OnceLock::new();

fn get_instance() -> &'static Singleton {
    INSTANCE.get_or_init(|| Singleton::new())
}
```

---

## 七、反例索引表

| 反例ID | 概念 | 难度 | 出现频率 |
| :--- | :--- | :--- | :--- |
| CE-1.1 | 所有权转移 | ⭐⭐ | 高 |
| CE-1.2 | 部分移动 | ⭐⭐⭐ | 中 |
| CE-2.1 | 借用冲突 | ⭐⭐ | 高 |
| CE-2.2 | 多重可变借用 | ⭐⭐ | 高 |
| CE-2.3 | 悬垂引用 | ⭐⭐⭐ | 中 |
| CE-3.1 | 生命周期省略 | ⭐⭐⭐ | 中 |
| CE-4.1 | Rc跨线程 | ⭐⭐⭐ | 中 |
| CE-4.2 | RefCell跨线程 | ⭐⭐⭐ | 中 |
| CE-5.1 | 跨await持锁 | ⭐⭐⭐⭐ | 低 |
| CE-6.1 | 单例模式 | ⭐⭐⭐ | 中 |

---

## 八、从反例学习

### 反例的教育价值

1. **理解边界**: 知道什么不能做
2. **深入原理**: 理解为什么这样设计
3. **记忆深刻**: 错误比正确更容易记住
4. **快速诊断**: 遇到错误能快速定位

### 学习建议

- 动手复现每个反例
- 修改代码看编译器反应
- 尝试不同的修复方案
- 总结模式，举一反三

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-23
**用途**: 通过反例理解Rust安全边界
