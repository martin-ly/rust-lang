# 闭包基础：捕获环境与匿名函数

> **Bloom 层级**: 理解 → 应用
> **定位**: 系统讲解 Rust **闭包（Closure）**——从环境捕获、Fn/FnMut/FnOnce trait 到闭包作为参数和返回值，揭示 Rust 如何将函数式编程的灵活性与所有权系统的安全性结合。
> **前置概念**: [Traits](../02_intermediate/01_traits.md) · [Ownership](./01_ownership.md) · [Borrowing](./02_borrowing.md)
> **后置概念**: [Iterator](../02_intermediate/16_iterator_patterns.md) · [Async](../03_advanced/02_async.md) · [Functional Patterns](../02_intermediate/07_closure_types.md)

---

> **来源**: [TRPL — Closures](https://doc.rust-lang.org/book/ch13-01-closures.html) · [Rust Reference — Closure Expressions](https://doc.rust-lang.org/reference/expressions/closure-expr.html) · [std::ops::Fn](https://doc.rust-lang.org/std/ops/trait.Fn.html) · [RFC 1558 — Closures](https://rust-lang.github.io/rfcs/1558-closure-to-fn-coercion.html) · [Wikipedia — Closure (computer programming)](https://en.wikipedia.org/wiki/Closure_(computer_programming))

## 📑 目录
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

- [闭包基础：捕获环境与匿名函数](#闭包基础捕获环境与匿名函数)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 闭包的语法与捕获](#11-闭包的语法与捕获)
    - [1.2 Fn / FnMut / FnOnce](#12-fn--fnmut--fnonce)
    - [1.3 闭包与所有权](#13-闭包与所有权)
  - [二、技术细节](#二技术细节)
    - [2.1 闭包作为函数参数](#21-闭包作为函数参数)
    - [2.2 闭包与类型推断](#22-闭包与类型推断)
    - [2.3 move 闭包](#23-move-闭包)
  - [三、闭包模式矩阵](#三闭包模式矩阵)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 边界极限](#42-边界极限)
  - [五、常见陷阱](#五常见陷阱)
  - [六、来源与延伸阅读](#六来源与延伸阅读)
  - [相关概念文件](#相关概念文件)

---

## 一、核心概念
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

### 1.1 闭包的语法与捕获

```rust,ignore
// 闭包的基本语法

// 1. 最简单的闭包
let add_one = |x| x + 1;
assert_eq!(add_one(5), 6);

// 2. 多参数
let add = |x, y| x + y;
assert_eq!(add(1, 2), 3);

// 3. 显式类型标注（通常可推断）
let add = |x: i32, y: i32| -> i32 { x + y };

// 4. 捕获环境
let factor = 2;
let multiply = |x| x * factor;  // factor 被捕获
assert_eq!(multiply(5), 10);

// 5. 多语句闭包
let process = |x: i32| -> i32 {
    let doubled = x * 2;
    let incremented = doubled + 1;
    incremented
};

// 捕获方式:
// ├── 不可变借用: &T（默认，如果可能）
// ├── 可变借用: &mut T（如果需要修改）
// └── 移动: T（使用 move 关键字）
```

> **认知功能**: Rust 闭包是**匿名函数 + 环境捕获**——编译器自动推断捕获方式，遵循所有权规则。
> [来源: [TRPL — Closures](https://doc.rust-lang.org/book/ch13-01-closures.html)]

---

### 1.2 Fn / FnMut / FnOnce

```rust,ignore
// 三种闭包 trait

// Fn: 不可变借用捕获，可多次调用
fn call_fn<F>(f: F)
where F: Fn() {
    f();
    f();  // 可以多次调用
}

// FnMut: 可变借用捕获，可多次调用
fn call_fn_mut<F>(mut f: F)
where F: FnMut() {
    f();
    f();  // 可以多次调用
}

// FnOnce: 移动捕获，只能调用一次
fn call_fn_once<F>(f: F)
where F: FnOnce() {
    f();
    // f();  // 编译错误！只能调用一次
}

// 自动推导:
let s = String::from("hello");

// Fn: 只读引用
let closure_fn = |x: &str| println!("{} {}", s, x);
// s 被 &String 捕获

// FnMut: 可变引用
let mut count = 0;
let mut closure_fn_mut = || {
    count += 1;  // count 被 &mut i32 捕获
};

// FnOnce: 移动所有权
let s = String::from("hello");
let closure_fn_once = move || {
    drop(s);  // s 被 move 进闭包
};

// 继承关系:
// Fn <: FnMut <: FnOnce
// 实现 Fn 自动实现 FnMut 和 FnOnce
// 实现 FnMut 自动实现 FnOnce
```

> **Trait 洞察**: **Fn/FnMut/FnOnce 是 Rust 闭包的核心类型系统**——它们精确描述了闭包对环境的访问方式。
> [来源: [std::ops::Fn](https://doc.rust-lang.org/std/ops/trait.Fn.html)]

---

### 1.3 闭包与所有权

```rust,ignore
// 闭包捕获与所有权的交互

// 场景 1: 不可变借用
let s = String::from("hello");
let c = |x| println!("{} {}", s, x);  // s 被 &String 捕获
c("world");
println!("{}", s);  // ✅ s 仍可用

// 场景 2: 可变借用
let mut v = vec![1, 2, 3];
let mut c = || v.push(4);  // v 被 &mut Vec 捕获
c();
// println!("{:?}", v);  // ❌ v 被闭包可变借用

// 场景 3: move 闭包
let s = String::from("hello");
let c = move || println!("{}", s);  // s 被 move 进闭包
c();
// println!("{}", s);  // ❌ s 已被 move

// 场景 4: 强制 copy 捕获
let x = 5;
let c = || println!("{}", x);  // x 被 &i32 捕获（i32: Copy）
c();
c();  // ✅ 可以多次调用（Fn）

// move 与 Copy 类型:
let x = 5;
let c = move || x;  // x 被 copy（不是 move）
println!("{}", x);  // ✅ i32 是 Copy
```

> **所有权洞察**: 闭包的**捕获方式由编译器自动推断**——但开发者可以通过 `move` 关键字强制移动捕获。
> [来源: [Rust Reference — Closure Expressions](https://doc.rust-lang.org/reference/expressions/closure-expr.html)]

---

## 二、技术细节
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

### 2.1 闭包作为函数参数

```rust,ignore
// 高阶函数：接受闭包作为参数

// 1. 简单高阶函数
fn apply_twice<F>(f: F, x: i32) -> i32
where F: Fn(i32) -> i32,
{
    f(f(x))
}

let result = apply_twice(|x| x + 1, 5);  // 7

// 2. 迭代器风格的高阶函数
fn filter_and_map<T, F, G>(
    items: Vec<T>,
    predicate: F,
    transform: G,
) -> Vec<i32>
where
    F: Fn(&T) -> bool,
    G: Fn(T) -> i32,
{
    items.into_iter()
        .filter(predicate)
        .map(transform)
        .collect()
}

// 3. 返回闭包（需要 'static 或显式生命周期）
fn make_adder(x: i32) -> impl Fn(i32) -> i32 {
    move |y| x + y  // x 被 move，闭包是 'static
}

let add_five = make_adder(5);
assert_eq!(add_five(10), 15);

// 4. 闭包 trait 对象（动态分发）
fn dynamic_closure(f: Box<dyn Fn(i32) -> i32>) -> i32 {
    f(42)
}
```

> **高阶洞察**: Rust 的**高阶函数**与闭包结合，提供了与函数式语言相当的表达能力，同时保持类型安全。
> [来源: [Rust By Example — Closures](https://doc.rust-lang.org/rust-by-example/fn/closures.html)]

---

### 2.2 闭包与类型推断

```rust,ignore
// 闭包的类型推断

// 编译器推断闭包类型:
let closure = |x| x + 1;
// 类型: 某种实现 Fn(i32) -> i32 的匿名结构体

// 每个闭包是唯一的类型！
let c1 = || {};
let c2 = || {};
// c1 和 c2 是不同的类型

// 但可以实现相同的 trait:
fn take_closure<F: Fn()>(f: F) {}
take_closure(c1);
take_closure(c2);  // ✅ 都满足 Fn()

// 闭包大小:
// ├── 空闭包: 0 字节（类似 unit 结构体）
// ├── 捕获一个引用: 8/16 字节（指针大小）
// ├── 捕获一个 String: 24 字节（ptr + len + cap）
// └── 闭包大小 = 捕获变量大小之和

// 闭包不能比较（除非实现特定 trait）:
// let c1 = || 1;
// let c2 = || 1;
// assert_eq!(c1, c2);  // ❌ 编译错误！

// 闭包可以强制转换为函数指针（如果无捕获）:
let f: fn(i32) -> i32 = |x| x + 1;
// 仅当闭包不捕获环境时
```

> **推断洞察**: 每个闭包是**唯一的匿名类型**——这是 Rust 实现零成本抽象的**关键设计**。
> [来源: [RFC 1558 — Closure to Fn Coercion](https://rust-lang.github.io/rfcs/1558-closure-to-fn-coercion.html)]

---

### 2.3 move 闭包

```rust,ignore
// move 关键字：强制按值捕获

// 场景 1: 延长生命周期
fn make_closure<'a>(s: &'a str) -> impl Fn() + 'a {
    // let c = || println!("{}", s);  // 可能不够长
    let c = move || println!("{}", s.to_string());  // 复制数据
    c
}

// 场景 2: 跨线程发送
let data = vec![1, 2, 3];
std::thread::spawn(move || {
    println!("{:?}", data);
}).join().unwrap();
// data 被 move 进新线程

// 场景 3: 在 async 中
let resource = get_resource();
let future = async move {
    use_resource(resource).await;
};
// resource 被 move 进 future

// move 与 Copy:
let x = 5;
let c = move || x;  // x 被 copy（不是 move）
println!("{}", x);  // ✅ i32: Copy

let s = String::from("hello");
let c = move || s;  // s 被 move
// println!("{}", s);  // ❌ s 已被 move

// move 与引用:
let s = String::from("hello");
let c = move || &s;  // ❌ 编译错误！s 被 move，无法返回引用
```

> **move 洞察**: `move` 是**控制闭包所有权的显式工具**——它在需要延长数据生命周期或跨线程/异步边界时使用。
> [来源: [TRPL — Move Closures](https://doc.rust-lang.org/book/ch13-01-closures.html#moving-captured-values-out-of-the-closure-and-the-fn-traits)]

---

## 三、闭包模式矩阵
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

```text
场景 → 闭包类型 → 使用方式

回调函数:
  → Fn / FnMut
  → 事件处理、回调注册
  → button.on_click(|| println!("clicked"));

迭代器适配:
  → Fn
  → map, filter, fold
  → items.iter().map(|x| x * 2)

延迟计算:
  → FnOnce / Fn
  → 惰性求值、缓存
  → once_cell::Lazy::new(|| expensive())

线程入口:
  → FnOnce + Send + 'static
  → thread::spawn(move || { ... })

async 块:
  → 类似闭包，但异步
  → async move { ... }

排序比较:
  → Fn(&T, &T) -> Ordering
  → items.sort_by(|a, b| a.cmp(b))
```

> **模式矩阵**: 闭包是 Rust **函数式编程风格的核心**——它们与迭代器、异步和并发深度集成。
> [来源: [Rust Patterns — Closures](https://rust-unofficial.github.io/patterns/patterns/functional/closure.html)]

---

## 四、反命题与边界分析
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

### 4.1 反命题树

```mermaid
graph TD
    ROOT["命题: 所有匿名函数都应使用闭包"]
    ROOT --> Q1{"是否需要捕获环境?"}
    Q1 -->|是| CLOSURE["✅ 闭包"]
    Q1 -->|否| Q2{"是否需要函数指针?"}
    Q2 -->|是| FN_PTR["✅ 函数指针 fn()"]
    Q2 -->|否| EITHER["⚠️ 均可"]

    style CLOSURE fill:#c8e6c9
    style FN_PTR fill:#c8e6c9
    style EITHER fill:#fff3e0
```

> **认知功能**: **不捕获环境时使用 fn 指针或普通函数**——它们更简单且有明确类型。
> [来源: [Rust API Guidelines — Functions](https://rust-lang.github.io/api-guidelines/naming.html)]

---

### 4.2 边界极限

```text
边界 1: 闭包类型的大小
├── 大捕获增加闭包大小
├── 闭包按值传递时复制开销
├── 建议 Box<dyn Fn()> 减少复制
└── 缓解: 使用 Rc/Arc 共享大捕获

边界 2: 递归闭包
├── 闭包不能直接递归调用自身
├── 需要 Y combinator 或固定点组合子
├── 复杂且不直观
└── 缓解: 使用普通递归函数

边界 3: 闭包与 Trait Object
├── Box<dyn Fn()> 有动态分发开销
├── 不适合性能关键路径
├── 但提供类型擦除能力
└── 缓解: 泛型参数（单态化）

边界 4: 生命周期复杂化
├── 捕获引用的闭包有生命周期约束
├── 返回借用闭包需要显式标注
├── 可能与 HRTB 交互
└── 缓解: 使用 owned 数据或 'static

边界 5: 调试困难
├── 闭包是匿名类型，调试信息有限
├── 堆栈跟踪中闭包名称不友好
├── 某些 IDE 对闭包支持有限
└── 缓解: 为重要闭包提供命名包装
```

> **边界要点**: 闭包的边界主要与**大小**、**递归**、**动态分发**、**生命周期**和**调试**相关。
> [来源: [Rust Reference — Closure Types](https://doc.rust-lang.org/reference/types/closure.html)]

---

## 五、常见陷阱
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

```text
陷阱 1: 可变捕获与多次调用冲突
  ❌ let mut s = String::from("hello");
     let c = || s.push_str(" world");  // FnMut
     call_fn(c);  // 需要 Fn

  ✅ let mut s = String::from("hello");
     let mut c = || s.push_str(" world");
     call_fn_mut(&mut c);

陷阱 2: 忘记 move 导致生命周期问题
  ❌ let s = String::from("hello");
     std::thread::spawn(|| println!("{}", s));
     // 编译错误：s 可能不够长

  ✅ std::thread::spawn(move || println!("{}", s));
     // s 被 move 进闭包

陷阱 3: 在闭包中返回局部引用
  ❌ let c = |x: &str| -> &str { let s = x.to_string(); &s };
     // 返回局部变量引用

  ✅ let c = |x: &str| -> String { x.to_string() };
     // 返回 owned 值

陷阱 4: 混淆 Fn trait bound
  ❌ fn takes_fn<F: FnOnce()>(f: F) { f(); f(); }
     // 只能调用一次

  ✅ fn takes_fn<F: Fn()>(f: F) { f(); f(); }
     // 可以多次调用

陷阱 5: 大闭包的性能问题
  ❌ 闭包捕获大量数据
     // 按值传递时复制开销大

  ✅ 使用 Rc/Arc 共享数据
     // 或 Box< dyn Fn() > 减少复制
```

> **陷阱总结**: 闭包的陷阱主要与**Fn trait 选择**、**move 遗漏**、**返回引用**、**多次调用**和**性能**相关。
> [来源: [Common Closure Mistakes](https://doc.rust-lang.org/rust-by-example/fn/closures.html)]

---

## 六、来源与延伸阅读

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [TRPL — Closures](https://doc.rust-lang.org/book/ch13-01-closures.html) | ✅ 一级 | 基础教程 |
| [std::ops::Fn](https://doc.rust-lang.org/std/ops/trait.Fn.html) | ✅ 一级 | Trait 文档 |
| [Rust Reference — Closures](https://doc.rust-lang.org/reference/expressions/closure-expr.html) | ✅ 一级 | 语法参考 |
| [RFC 1558](https://rust-lang.github.io/rfcs/1558-closure-to-fn-coercion.html) | ✅ 一级 | 闭包设计 |
| [Rust By Example — Closures](https://doc.rust-lang.org/rust-by-example/fn/closures.html) | ✅ 一级 | 示例 |

---

## 相关概念文件
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

- [Traits](../02_intermediate/01_traits.md) — Trait 系统
- [Ownership](./01_ownership.md) — 所有权
- [Iterator](../02_intermediate/16_iterator_patterns.md) — 迭代器
- [Async](../03_advanced/02_async.md) — 异步编程

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/)
>
> **权威来源对齐变更日志**: 2026-05-22 创建 [来源: Authority Source Sprint Batch 10]

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-22
**状态**: ✅ 概念文件创建完成
