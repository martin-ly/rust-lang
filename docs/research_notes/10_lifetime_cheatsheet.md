# 生命周期速查卡 {#生命周期速查卡}

> **EN**: Lifetime Cheatsheet
> **Summary**: 生命周期（Lifetimes）速查卡 Lifetime Cheatsheet.
>
> **概念族**: 速查卡
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) | [The Rust Programming Language](https://doc.rust-lang.org/book/) | [Rustonomicon](https://doc.rust-lang.org/nomicon/) | [NLL RFC](https://rust-lang.github.io/rfcs/2094-nll.html)
> **创建日期**: 2026-02-10
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ 已完成权威国际化来源对齐升级
> **一页纸速查** - 生命周期语法、规则、常见模式

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [生命周期速查卡 {#生命周期速查卡}](#生命周期速查卡-生命周期速查卡)
  - [📑 目录 {#目录}](#-目录-目录)
  - [生命周期语法 {#生命周期语法}](#生命周期语法-生命周期语法)
  - [生命周期省略（Lifetime Elision）规则 {#生命周期省略规则-1}](#生命周期省略规则-生命周期省略规则-1)
  - [结构体（Struct）生命周期 {#结构体生命周期-1}](#结构体生命周期-结构体生命周期-1)
  - ['static 生命周期 {#static-生命周期}](#static-生命周期-static-生命周期)
  - [高阶Trait Bound (HRTB) {#高阶trait（Trait）-bound-hrtb}](#高阶trait-bound-hrtb-高阶trait-bound-hrtb)
  - [常见模式 {#常见模式}](#常见模式-常见模式)
    - [输入输出相同生命周期 {#输入输出相同生命周期}](#输入输出相同生命周期-输入输出相同生命周期)
    - [返回与特定输入关联 {#返回与特定输入关联}](#返回与特定输入关联-返回与特定输入关联)
    - [多个输入，返回其中一个 {#多个输入返回其中一个}](#多个输入返回其中一个-多个输入返回其中一个)
  - [生命周期错误与修复 {#生命周期错误与修复}](#生命周期错误与修复-生命周期错误与修复)
  - [Trait对象生命周期 {#trait对象（Trait Object）生命周期}](#trait对象生命周期-trait对象生命周期)
  - [型变与生命周期 {#型变与生命周期}](#型变与生命周期-型变与生命周期)
  - [与泛型（Generics）结合 {#与泛型结合}](#与泛型结合-与泛型结合)
  - [自我引用（Reference）结构 {#自我引用结构}](#自我引用结构-自我引用结构)
  - [快速诊断 {#快速诊断}](#快速诊断-快速诊断)
  - [生命周期基础 {#生命周期基础}](#生命周期基础-生命周期基础)
    - [生命周期关系 {#生命周期关系}](#生命周期关系-生命周期关系)
    - [常见生命周期 {#常见生命周期}](#常见生命周期-常见生命周期)
  - [生命周期省略规则 {#生命周期省略规则-1}](#生命周期省略规则-生命周期省略规则-1-1)
    - [三条规则 {#三条规则}](#三条规则-三条规则)
    - [示例 {#示例}](#示例-示例)
  - [常见生命周期模式 {#常见生命周期模式}](#常见生命周期模式-常见生命周期模式)
    - [模式1: 输入输出相同 {#模式1-输入输出相同}](#模式1-输入输出相同-模式1-输入输出相同)
    - [模式2: 返回self的引用 {#模式2-返回self的引用}](#模式2-返回self的引用-模式2-返回self的引用)
    - [模式3: 独立生命周期 {#模式3-独立生命周期}](#模式3-独立生命周期-模式3-独立生命周期)
  - [生命周期约束 {#生命周期约束}](#生命周期约束-生命周期约束)
    - [HRTB (高阶trait bound) {#hrtb-高阶trait-bound}](#hrtb-高阶trait-bound-hrtb-高阶trait-bound)
    - [多重约束 {#多重约束}](#多重约束-多重约束)
  - [常见错误 {#常见错误}](#常见错误-常见错误)
    - [错误1: 返回局部引用 {#错误1-返回局部引用}](#错误1-返回局部引用-错误1-返回局部引用)
    - [错误2: 生命周期不匹配 {#错误2-生命周期不匹配}](#错误2-生命周期不匹配-错误2-生命周期不匹配)
  - [结构体生命周期 {#结构体生命周期-1}](#结构体生命周期-结构体生命周期-1-1)
  - [生命周期与子类型 {#生命周期与子类型}](#生命周期与子类型-生命周期与子类型)
  - [技巧 {#技巧}](#技巧-技巧)
    - [技巧1: `'static`默认 {#技巧1-static默认}](#技巧1-static默认-技巧1-static默认)
    - [技巧2: 生命周期推断 {#技巧2-生命周期推断}](#技巧2-生命周期推断-技巧2-生命周期推断)
    - [技巧3: 显式drop {#技巧3-显式drop}](#技巧3-显式drop-技巧3-显式drop)
  - [快速决策 {#快速决策}](#快速决策-快速决策)
  - [🌍 权威国际化资源链接 {#权威国际化资源链接}](#-权威国际化资源链接-权威国际化资源链接)
    - [Rust Reference 核心章节 {#rust-reference-核心章节}](#rust-reference-核心章节-rust-reference-核心章节)
    - [The Rust Programming Language 核心章节 {#the-rust-programming-language-核心章节}](#the-rust-programming-language-核心章节-the-rust-programming-language-核心章节)
    - [Rust Standard Library 核心 API / 模块（Module） {#rust-standard-library-核心-api-模块}](#rust-standard-library-核心-api--模块-rust-standard-library-核心-api-模块)
    - [Rust By Example / Rust Cookbook / cheats.rs {#rust-by-example-rust-cookbook-cheatsrs}](#rust-by-example--rust-cookbook--cheatsrs-rust-by-example-rust-cookbook-cheatsrs)
    - [生命周期专属权威链接 {#生命周期专属权威链接}](#生命周期专属权威链接-生命周期专属权威链接)
      - [Reference Lifetime 章节 {#reference-lifetime-章节}](#reference-lifetime-章节-reference-lifetime-章节)
      - [Rust By Example / Cookbook / cheats.rs {#rust-by-example-cookbook-cheatsrs}](#rust-by-example--cookbook--cheatsrs-rust-by-example-cookbook-cheatsrs)
      - [NLL / RustBelt / Stacked Borrows {#nll-rustbelt-stacked-borrows}](#nll--rustbelt--stacked-borrows-nll-rustbelt-stacked-borrows)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 生命周期语法 {#生命周期语法}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
// 显式标注
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str

// 多个独立生命周期
fn parse<'a, 'b>(input: &'a str, config: &'b Config) -> &'a Token

// 生命周期约束
fn process<'a, 'b>(x: &'a Data, y: &'b Data) -> &'a Data
where
    'a: 'b,  // 'a 至少和 'b 一样长
```

---

## 生命周期省略规则 {#生命周期省略规则-1}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

编译器自动应用以下规则：

1. **每个引用参数有独立生命周期**

   ```rust,ignore
   fn foo(x: &i32, y: &i32)  // 隐式: fn foo<'a, 'b>(x: &'a i32, y: &'b i32)
   ```

2. **单一输入生命周期应用到输出**

   ```rust,ignore
   fn foo(x: &i32) -> &i32   // 隐式: fn foo<'a>(x: &'a i32) -> &'a i32
   ```

3. **`&self`的生命周期应用到输出**

   ```rust,ignore
   fn foo(&self) -> &T       // 隐式: fn foo<'a>(&'a self) -> &'a T
   fn foo(&self, x: &T) -> &T  // 规则1+3: fn foo<'a, 'b>(&'a self, x: &'b T) -> &'a T
   ```

---

## 结构体生命周期 {#结构体生命周期-1}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
// 持有引用需要生命周期参数
struct Parser<'a> {
    input: &'a str,
    position: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Self { input, position: 0 }
    }

    fn peek(&self) -> Option<&'a str> {
        // 返回与输入相同生命周期的引用
        self.input.get(self.position..self.position+1)
    }
}
```

---

## 'static 生命周期 {#static-生命周期}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
// 字符串字面量是'static
let s: &'static str = "I live forever";

// 与泛型结合
fn spawn_thread<F>(f: F)
where
    F: FnOnce() + 'static,  // 闭包不捕获非'static引用
{}

// 全局常量
static GLOBAL: i32 = 42;
```

---

## 高阶Trait Bound (HRTB) {#高阶trait-bound-hrtb}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
// 对所有生命周期都成立
fn call_with_ref<F>(f: F)
where
    F: for<'a> Fn(&'a str),
{
    f("hello");
}

// 与闭包一起使用
let closure = |s: &str| println!("{}", s);
call_with_ref(closure);
```

---

## 常见模式 {#常见模式}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 输入输出相同生命周期 {#输入输出相同生命周期}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
fn identity<'a>(x: &'a str) -> &'a str {
    x
}
```

### 返回与特定输入关联 {#返回与特定输入关联}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
fn get_name<'a>(person: &'a Person) -> &'a str {
    &person.name
}
```

### 多个输入，返回其中一个 {#多个输入返回其中一个}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_System)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
fn choose<'a>(first: &'a str, second: &'a str, use_first: bool) -> &'a str {
    if use_first { first } else { second }
}
```

---

## 生命周期错误与修复 {#生命周期错误与修复}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 错误 | 代码 | 修复 |
| :--- | :--- | :--- |
| 悬垂引用 | `fn bad() -> &str { let s = ""; &s }` | 返回 `String` 或 `'static` |
| 生命周期不匹配 | `let r; { let x = 5; r = &x; }` | 扩大值的作用域 |
| 借用（Borrowing）冲突 | `&mut` 同时有 `&` | 分离使用范围 |

---

## Trait对象生命周期 {#trait对象生命周期}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
// 默认'static
trait Trait {}
Box<dyn Trait>           // Box<dyn Trait + 'static>

// 显式生命周期
trait Parser<'a> {}
Box<dyn Parser<'a> + 'a>

// 省略形式
trait Read {}
&dyn Read                // &'_ dyn Read (匿名生命周期)
```

---

## 型变与生命周期 {#型变与生命周期}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust
// &'a T 对 'a 协变
// &'a T <: &'b T  当 'a: 'b (a比b长)

fn example() {
    let s: &'static str = "static";
    let r: &str = s;  // OK: 'static <: any lifetime
}

// &'a mut T 对 'a 不变
// &'a mut T 对 T 不变
```

---

## 与泛型结合 {#与泛型结合}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
// 泛型函数带生命周期
fn process<'a, T>(data: &'a [T]) -> impl Iterator<Item = &'a T> {
    data.iter()
}

// 泛型结构体
struct Wrapper<'a, T: 'a> {
    data: &'a T,
}

// Trait Bound
fn use_display<'a, T>(x: &'a T) -> &'a T
where
    T: Display + 'a,
{ x }
```

---

## 自我引用结构 {#自我引用结构}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust
// 需要Pin
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfReferential {
    data: String,
    ptr_to_data: *const String,
    _pin: PhantomPinned,
}

impl SelfReferential {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::pin(Self {
            data,
            ptr_to_data: std::ptr::null(),
            _pin: PhantomPinned,
        });

        let ptr = &boxed.data as *const String;
        unsafe {
            boxed.as_mut().get_unchecked_mut().ptr_to_data = ptr;
        }

        boxed
    }
}
```

---

## 快速诊断 {#快速诊断}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```
错误: "borrowed value does not live long enough"
原因: 引用的值比引用先死
解决: 扩大值作用域或改变所有权

错误: "lifetime mismatch"
原因: 输入输出生命周期不匹配
解决: 添加生命周期标注或调整返回类型

错误: "cannot return reference to local variable"
原因: 返回局部变量的引用
解决: 返回值所有权或'static
```

## 生命周期基础 {#生命周期基础}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### 生命周期关系 {#生命周期关系}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**

```rust,ignore
'a: 'b  // 'a 至少和 'b 一样长（'a 包含 'b）
T: 'a   // T 中所有引用至少存活 'a
```

### 常见生命周期 {#常见生命周期}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

| 标注 | 含义 | 示例 |
| :--- | :--- | :--- |
| `'static` | 程序整个运行期间 | `&'static str` |
| `'a` | 泛型生命周期 | `&'a i32` |
| `'_` | 让编译器推断 | `&'_ i32` |

---

## 生命周期省略规则 {#生命周期省略规则-1}
>
> **[来源: [crates.io](https://crates.io/)]**

### 三条规则 {#三条规则}

> **来源: [IEEE](https://standards.ieee.org/)**

```
1. 每个引用参数有自己的生命周期
2. 只有一个输入生命周期 → 赋给所有输出
3. `&self`/`&mut self`存在 → self的生命周期赋给输出
```

### 示例 {#示例}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

```rust,ignore
// 省略前
fn foo<'a>(x: &'a str) -> &'a str { x }

// 省略后
fn foo(x: &str) -> &str { x }  // 规则2

// 方法省略
fn method(&self, x: &str) -> &str { self.0 }
// 等价于: fn method<'a, 'b>(&'a self, x: &'b str) -> &'a str
```

---

## 常见生命周期模式 {#常见生命周期模式}
>
> **[来源: [docs.rs](https://docs.rs/)]**

### 模式1: 输入输出相同 {#模式1-输入输出相同}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

### 模式2: 返回self的引用 {#模式2-返回self的引用}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

```rust,ignore
impl<'a> Parser<'a> {
    fn input(&self) -> &'a str { self.input }
}
```

### 模式3: 独立生命周期 {#模式3-独立生命周期}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

```rust,ignore
fn parse<'a, 'b>(input: &'a str, config: &'b Config) -> &'a str {
    // 返回与input关联的数据
}
```

---

## 生命周期约束 {#生命周期约束}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### HRTB (高阶trait bound) {#hrtb-高阶trait-bound}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
F: for<'a> Fn(&'a str) -> &'a str
```

### 多重约束 {#多重约束}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
trait Foo<'a, 'b>
where
    'a: 'b,  // 'a 至少和 'b 一样长
    T: 'a,   // T 中所有引用至少 'a
{}
```

---

## 常见错误 {#常见错误}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 错误1: 返回局部引用 {#错误1-返回局部引用}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust,ignore
// ❌ 错误
fn bad() -> &str {
    let s = String::from("hello");
    &s  // s 在函数结束时被释放
}

// ✅ 修复
fn good() -> String {
    String::from("hello")  // 转移所有权
}
```

### 错误2: 生命周期不匹配 {#错误2-生命周期不匹配}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```rust,ignore
// ❌ 错误
fn longest(x: &str, y: &str) -> &str { ... }

// ✅ 修复
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str { ... }
```

---

## 结构体生命周期 {#结构体生命周期-1}
>
> **[来源: [crates.io](https://crates.io/)]**

```rust
struct Person<'a> {
    name: &'a str,  // name 必须活得比 Person 长
}

// 使用
let name = String::from("Alice");
let p = Person { name: &name };
// name 必须在这里之后才能 drop
```

---

## 生命周期与子类型 {#生命周期与子类型}
>
> **[来源: [docs.rs](https://docs.rs/)]**

```
'static <: 'a <: 'b <: ...

长生命周期是短生命周期的子类型
```

```rust
let s: &'static str = "hello";
take_str(s);  // 可以传给需要 &'a str 的函数

fn take_str<'a>(s: &'a str) {}
```

---

## 技巧 {#技巧}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 技巧1: `'static`默认 {#技巧1-static默认}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust
// 拥有所有权的类型隐式 'static
struct OwnedData {
    data: String,  // 等价于 data: String + 'static
}
```

### 技巧2: 生命周期推断 {#技巧2-生命周期推断}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
// 大多数情况下不需要显式标注
let r = &x;  // 编译器自动推断
```

### 技巧3: 显式drop {#技巧3-显式drop}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust,ignore
{
    let r = &x;
    // 使用 r
    drop(r);  // 显式结束借用
}  // 或等待作用域结束
// 现在可以修改 x 了
```

---

## 快速决策 {#快速决策}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```text
需要显式生命周期？
├── 返回引用？
│   ├── 来自参数 → 标注与参数相同
│   └── 来自self → 标注self的生命周期
├── 结构体包含引用？
│   └── 需要生命周期参数
└── 泛型约束？
    └── T: 'a
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 🌍 权威国际化资源链接 {#权威国际化资源链接}
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)**
> **来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)**
> **来源: [cheats.rs](https://cheats.rs/)**

本节为速查内容提供官方权威来源与社区经典参考的直通链接，便于深入验证与扩展阅读。

### Rust Reference 核心章节 {#rust-reference-核心章节}

- [Reference 首页](https://doc.rust-lang.org/reference/)
- [Types](https://doc.rust-lang.org/reference/types.html)
- [Items / Traits](https://doc.rust-lang.org/reference/items/traits.html)
- [Expressions](https://doc.rust-lang.org/reference/expressions.html)
- [Statements](https://doc.rust-lang.org/reference/statements.html)
- [Crates and Source Files](https://doc.rust-lang.org/reference/crates-and-source-files.html)

### The Rust Programming Language 核心章节 {#the-rust-programming-language-核心章节}

- [TRPL 首页](https://doc.rust-lang.org/book/)
- [Ch. 4 - Understanding Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [Ch. 9 - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [Ch. 10 - Generic Types, Traits, Lifetimes](https://doc.rust-lang.org/book/ch10-00-generics.html)
- [Ch. 13 - Closures](https://doc.rust-lang.org/book/ch13-00-functional-features.html)
- [Ch. 15 - Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)
- [Ch. 16 - Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [Ch. 19 - Advanced Features / Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)

### Rust Standard Library 核心 API / 模块 {#rust-standard-library-核心-api-模块}

- [std 首页](https://doc.rust-lang.org/std/)
- [std::result](https://doc.rust-lang.org/std/result/)
- [std::option](https://doc.rust-lang.org/std/option/)
- [std::error::Error](https://doc.rust-lang.org/std/error/trait.Error.html)
- [std::fmt](https://doc.rust-lang.org/std/fmt/)
- [std::panic](https://doc.rust-lang.org/std/panic/)
- [std::marker (Send / Sync / PhantomData)](https://doc.rust-lang.org/std/marker/)

### Rust By Example / Rust Cookbook / cheats.rs {#rust-by-example-rust-cookbook-cheatsrs}

- [Rust By Example 首页](https://doc.rust-lang.org/rust-by-example/)
- [Rust Cookbook 首页](https://rust-lang-nursery.github.io/rust-cookbook/)
- [cheats.rs 首页](https://cheats.rs/)

---

### 生命周期专属权威链接 {#生命周期专属权威链接}

> **来源: [Rust Reference - Lifetimes](https://doc.rust-lang.org/reference/lifetime-elision.html)**
> **来源: [TRPL Ch. 10 - Lifetimes](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)**

#### Reference Lifetime 章节 {#reference-lifetime-章节}

- [Lifetime Elision](https://doc.rust-lang.org/reference/lifetime-elision.html)
- [Trait and Lifetime Bounds](https://doc.rust-lang.org/reference/trait-bounds.html)
- [Higher-ranked Trait Bounds](https://doc.rust-lang.org/reference/higher-ranked-trait-bounds.html)
- [Subtyping and Variance](https://doc.rust-lang.org/reference/subtyping-and-variance.html)

#### Rust By Example / Cookbook / cheats.rs {#rust-by-example-cookbook-cheatsrs}

- [RBE - Lifetimes](https://doc.rust-lang.org/rust-by-example/scope/lifetime.html)
- [RBE - Lifetime Elision](https://doc.rust-lang.org/rust-by-example/scope/lifetime/elision.html)
- [cheats.rs - Lifetimes](https://cheats.rs/#lifetimes)

#### NLL / RustBelt / Stacked Borrows {#nll-rustbelt-stacked-borrows}

- [RFC 2094 - Non-Lexical Lifetimes (NLL)](https://rust-lang.github.io/rfcs/2094-nll.html)
- [RustBelt: Securing the Foundations of the Rust Programming Language](https://plv.mpi-sws.org/rustbelt/)
- [RustBelt paper (PDF)](https://plv.mpi-sws.org/rustbelt/rustbelt.pdf)
- [Stacked Borrows](https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/stacked-borrows.md)
- [Rustonomicon - Ownership](https://doc.rust-lang.org/nomicon/ownership.html)
- [Rustonomicon - Lifetimes](https://doc.rust-lang.org/nomicon/lifetimes.html)

## 相关概念 {#相关概念}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Variable Scope](https://en.wikipedia.org/wiki/Variable_Scope)**
> **来源: [TRPL Ch. 10 - Lifetimes](https://doc.rust-lang.org/book/ch10-00-generics.html)**
> **来源: [Rust Reference - Lifetimes](https://doc.rust-lang.org/reference/lifetime-elision.html)**
> **来源: [RFC 2094 - NLL](https://rust-lang.github.io/rfcs/2094-nll.html)**
> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

---
