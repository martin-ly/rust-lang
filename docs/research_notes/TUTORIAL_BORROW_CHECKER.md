# 教程：理解借用检查器

> **创建日期**: 2026-02-24
> **最后更新**: 2026-02-28
> **目标受众**: 初学者-进阶
> **预计阅读时间**: 30分钟
> **级别**: L1/L2

---

## 引言

借用检查器(Borrow Checker)是Rust编译器的核心组件，它在编译时检查代码的内存安全性，确保没有数据竞争、悬垂指针或使用已释放内存等问题。本教程将帮助你理解借用检查器的工作原理。

---

## 第一部分：为什么需要借用检查器

### 内存安全威胁

在传统语言中，以下问题是常见的：

```c
// C语言示例: 悬垂指针
char* bad() {
    char buffer[100] = "hello";
    return buffer;  // 返回局部变量的指针!
}
// buffer在函数结束时被释放，返回的指针指向无效内存
```

```c
// C语言示例: 数据竞争
int counter = 0;

void thread1() { counter++; }
void thread2() { counter++; }
// 没有同步，结果不确定!
```

### Rust的解决方案

Rust在编译时阻止这些问题：

```rust
// Rust: 编译错误!
fn bad() -> &String {
    let buffer = String::from("hello");
    &buffer  // 错误: 返回局部变量的引用
}
```

```rust
// Rust: 编译错误!
let mut counter = 0;
let ref1 = &mut counter;
let ref2 = &mut counter;  // 错误: 不能有两个可变借用
```

---

## 第二部分：借用规则

### 三大规则

1. **同一时间，只能有一个可变借用 (`&mut T`)**
2. **可以有多个不可变借用 (`&T`)**
3. **不能同时存在可变和不可变借用**

### 规则的可视化

```
时间点 ──────────────────────────────────────>

所有者: [===== own =====]
          │         │
          │         └── 离开作用域，值被释放
          └── 创建值

借用场景1 - 多个不可变借用:
时间:    t1    t2    t3    t4    t5
借用1:   [====&====]
借用2:      [====&====]
借用3:         [=&=]
         ↑         ↑
         全部允许! 没有冲突

借用场景2 - 单个可变借用:
时间:    t1    t2    t3    t4    t5
借用:    [====&mut====]
         ↑              ↑
         OK - 只有一个可变借用

借用场景3 - 冲突:
时间:    t1    t2    t3    t4    t5
不可变:  [====&====]
可变:          [====&mut====]
               ↑
               冲突! 编译错误
```

---

## 第三部分：不可变借用

### 基本用法

```rust
let s = String::from("hello");

let r1 = &s;  // 不可变借用1
let r2 = &s;  // 不可变借用2
let r3 = &s;  // 不可变借用3 - 允许!

println!("{}, {}, {}", r1, r2, r3);
```

### 为什么多个不可变借用是安全的

因为不可变借用保证不修改数据，所以多个读者不会相互影响：

```
读者1 ──> 读取数据 <── 读者2
          ↑
          读者3

没有人修改数据，所以同时读取是安全的
```

---

## 第四部分：可变借用

### 独占性保证

```rust
let mut s = String::from("hello");

let r1 = &mut s;
// let r2 = &mut s;  // 错误! 不能有两个可变借用

r1.push_str(" world");
println!("{}", r1);

// r1不再使用，可以创建新的借用
let r2 = &mut s;  // OK!
r2.push_str("!");
```

### 为什么需要独占性

可变借用允许修改数据，如果同时有两个可变借用：

```rust
// 如果这被允许(实际上不是)
let r1 = &mut vec;
let r2 = &mut vec;

r1.push(1);  // 可能使r2的指针失效
r2[0];       // 悬垂指针! 未定义行为!
```

Rust阻止这种情况，保证内存安全。

---

## 第五部分：可变与不可变借用冲突

### 典型的冲突场景

```rust
let mut s = String::from("hello");

let r1 = &s;      // 不可变借用
let r2 = &s;      // 另一个不可变借用 - OK
let r3 = &mut s;  // 错误! 不能同时有可变和不可变

println!("{}, {}", r1, r2);
```

### 编译器错误分析

```
error[E0502]: cannot borrow `s` as mutable because it is also borrowed as immutable
 --> src/main.rs:5:14
  |
3 |     let r1 = &s;
  |              -- immutable borrow occurs here
4 |     let r2 = &s;
  |              -- immutable borrow occurs here
5 |     let r3 = &mut s;
  |              ^^^^^^ mutable borrow occurs here
6 |     println!("{}, {}", r1, r2);
  |                       -- immutable borrow later used here
```

### 解决冲突

```rust
let mut s = String::from("hello");

{
    let r1 = &s;
    let r2 = &s;
    println!("{}, {}", r1, r2);
} // 不可变借用在这里结束

let r3 = &mut s;  // OK! 现在可以可变借用了
r3.push_str(" world");
```

---

## 第六部分：NLL (非词法生命周期)

### 什么是NLL

Rust 2018引入了非词法生命周期，借用不再局限于词法作用域：

```rust
let mut s = String::from("hello");

let r = &s;
println!("{}", r);  // r最后一次使用

// r不再使用，可以创建可变借用
let r2 = &mut s;  // 在NLL之前这会失败!
r2.push_str(" world");
```

### NLL的效果

```
词法生命周期 (旧):
{
    let r = &s;      // ──┐
    println!("{}", r); //  │ 借用持续整个块
}                     // ──┘

非词法生命周期 (新):
{
    let r = &s;      // ─┐
    println!("{}", r); // 借用只到这里
    // ────────────────┘
    let r2 = &mut s;  // OK!
}
```

---

## 第七部分：借用与数据结构

### 结构体中的借用

```rust
struct Parser<'a> {
    input: &'a str,  // Parser借用外部字符串
    position: usize,
}

fn main() {
    let text = String::from("hello world");

    {
        let parser = Parser {
            input: &text,
            position: 0,
        };
        // 使用parser
    } // parser结束，借用释放

    // text仍然可用
    println!("{}", text);
}
```

### 自引用结构的问题

```rust
// 这不能编译!
struct SelfRef {
    data: String,
    ptr: &String,  // 指向data的引用
}

// 原因: 如果SelfRef被移动，data的地址改变，ptr变成悬垂指针
```

**解决方案**: 使用 `Pin` 或索引代替指针。

---

## 第八部分：常见编译错误与解决

### 错误1: 值被移动后使用

```rust
let s = String::from("hello");
let s2 = s;
println!("{}", s);  // 错误! s已被移动

// 解决: 克隆
let s2 = s.clone();
println!("{}", s);  // OK
```

### 错误2: 在借用期间修改

```rust
let mut s = String::from("hello");
let r = &s;
s.push_str(" world");  // 错误! s被借用
println!("{}", r);

// 解决: 分离借用和修改
let r = &s;
println!("{}", r);  // 借用结束
s.push_str(" world");  // OK
```

### 错误3: 返回局部引用

```rust
fn bad() -> &String {
    let s = String::from("hello");
    &s  // 错误! s在函数结束时释放
}

// 解决1: 返回所有权
fn good1() -> String {
    String::from("hello")
}

// 解决2: 返回'static
fn good2() -> &'static str {
    "hello"
}
```

---

## 第九部分：内部可变性

### 当借用规则太严格时

有时需要在有不可变引用的情况下修改数据：

```rust
use std::cell::RefCell;

let cell = RefCell::new(5);

let mut r1 = cell.borrow_mut();  // 运行时检查的可变借用
*r1 += 1;

// RefCell在运行时检查借用规则，违反会panic
```

### 内部可变性模式

| 类型 | 使用场景 | 线程安全 |
| :--- | :--- | :--- |
| `Cell<T>` | `Copy`类型，替换值 | 否 |
| `RefCell<T>` | 运行时借用检查 | 否 |
| `Mutex<T>` | 线程互斥访问 | 是 |
| `RwLock<T>` | 线程多读单写 | 是 |

---

## 第十部分：形式化视角

### 借用检查器的保证

**定理**: 通过Rust编译器检查的代码保证：

1. 没有悬垂指针
2. 没有双重释放
3. 没有数据竞争
4. 没有使用未初始化内存

### 与形式化定义的关联

| 概念 | 形式化定义 | 文档 |
| :--- | :--- | :--- |
| 借用 | `&'a T`, `&'a mut T` | borrow_checker_proof.md |
| 生命周期 | `'a: 'b` | lifetime_formalization.md |
| 数据竞争自由 | `Send` + `Sync` | send_sync_formalization.md |

---

## 总结

```
借用检查器核心
    │
    ├── 不可变借用 &T
    │   ├── 多个同时存在
    │   └── 只读访问
    │
    ├── 可变借用 &mut T
    │   ├── 唯一存在
    │   └── 读写访问
    │
    ├── 规则
    │   ├── &T 和 &mut T 不能共存
    │   └── 同一时间最多一个 &mut T
    │
    └── 结果
        ├── 编译期内存安全
        └── 零运行时开销
```

## 引言

借用检查器(Borrow Checker)是Rust编译器的核心组件。它确保你的代码内存安全，无需垃圾回收器。本教程将解释借用检查器的工作原理。

---

## 第一部分：为什么需要借用检查器？

### 内存安全问题

```rust
// C语言中的错误
int* ptr = malloc(sizeof(int));
free(ptr);
*ptr = 42;  // 使用已释放内存！悬垂指针！
```

传统解决方案：

- **GC**: 运行时开销
- **手动管理**: 容易出错
- **智能指针**: 仍可能出错

**Rust的解决方案**: 编译时检查，零运行时开销。

---

## 第二部分：借用检查器的核心规则

### 规则1: 要么多个不可变借用，要么一个可变借用

```rust
let mut x = 5;

// 可以有多个不可变借用
let r1 = &x;
let r2 = &x;
println!("{} {}", r1, r2);

// 但不能同时有可变借用
// let r3 = &mut x;  // 错误！
```

**为什么?** 防止数据竞争。读者看到的数据可能被写者修改。

### 规则2: 引用必须始终有效

```rust
let r;
{
    let x = 5;
    r = &x;  // 错误！x在此处被释放
}  // x结束
// r仍然有效，但指向无效内存
```

---

## 第三部分：工作原理

### 借用检查算法

```
1. 为每个引用分配生命周期
2. 检查引用是否活得比数据长
3. 检查借用规则冲突
4. 如果有冲突，编译错误
```

### 生命周期标注

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// 编译器检查:
// - 返回的引用与x、y生命周期关联
// - 调用者必须确保返回的引用活得足够长
```

---

## 第四部分：常见错误与解决

### 错误1: 借用冲突

```rust
let mut x = 5;
let r1 = &x;
let r2 = &mut x;  // 错误！r1还在用
println!("{}", r1);

// 解决: 缩小r1的作用域
{
    let r1 = &x;
    println!("{}", r1);
}
let r2 = &mut x;  // OK
```

### 错误2: 悬垂引用

```rust
fn dangling() -> &String {
    let s = String::from("hello");
    &s  // 错误！s在函数结束时被释放
}

// 解决: 返回所有权
fn not_dangling() -> String {
    let s = String::from("hello");
    s  // 转移所有权
}
```

---

## 第五部分：高级特性

### NLL (非词法生命周期)

```rust
let mut x = 5;
let y = &x;
println!("{}", y);  // y最后一次使用
// 这里y已经结束，即使还在作用域内
let z = &mut x;  // OK！NLL允许
```

### 内部可变性

```rust
use std::cell::RefCell;

let x = RefCell::new(5);
let y = x.borrow();    // 不可变借用
let z = x.borrow_mut(); // 运行时错误！已有借用
```

借用检查器在编译时检查，RefCell在运行时检查。

---

## 第六部分：形式化视角

### 定理 T-BR1

**借用检查器保证数据竞争自由。**

```
BorrowCheck(P) = OK → DataRaceFree(P)
```

**证明思路**:

- 借用规则确保写操作独占
- 不可变借用允许多个读者
- 不可能同时存在写者和读者

---

## 总结

```
借用检查器
    │
    ├──→ 核心规则
    │       ├── 要么多&，要么一个&mut
    │       └── 引用必须有效
    │
    ├──→ 实现方式
    │       ├── 生命周期分析
    │       └── 借用图检查
    │
    └──→ 保证
            ├── 无数据竞争
            ├── 无悬垂指针
            └── 零运行时开销
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 已扩展 - 借用检查器教程完整版
