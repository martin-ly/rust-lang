# 生命周期概念卡片 (Lifetime Concept Card)

> Rust引用的有效性保证机制

---

## 目录

- [生命周期概念卡片 (Lifetime Concept Card)](#生命周期概念卡片-lifetime-concept-card)
  - [目录](#目录)
  - [1. 概念定义](#1-概念定义)
    - [1.1 什么是生命周期](#11-什么是生命周期)
    - [1.2 直观理解](#12-直观理解)
    - [1.3 为什么需要生命周期](#13-为什么需要生命周期)
  - [2. 形式化理论](#2-形式化理论)
    - [2.1 生命周期作为区域](#21-生命周期作为区域)
    - [2.2 子类型关系](#22-子类型关系)
    - [2.3 借用检查的形式化](#23-借用检查的形式化)
  - [3. 生命周期标注](#3-生命周期标注)
    - [3.1 显式标注语法](#31-显式标注语法)
    - [3.2 典型标注模式](#32-典型标注模式)
    - [3.3 结构体生命周期](#33-结构体生命周期)
    - [3.4 Trait对象生命周期](#34-trait对象生命周期)
  - [4. 省略规则](#4-省略规则)
    - [4.1 生命周期省略规则](#41-生命周期省略规则)
    - [4.2 无法省略的情况](#42-无法省略的情况)
    - [4.3 方法中的生命周期](#43-方法中的生命周期)
  - [5. 高级特性](#5-高级特性)
    - [5.1 NLL (Non-Lexical Lifetimes)](#51-nll-non-lexical-lifetimes)
    - [5.2 生命周期约束](#52-生命周期约束)
    - [5.3 Higher-Ranked Trait Bounds (HRTB)](#53-higher-ranked-trait-bounds-hrtb)
    - [5.4 匿名生命周期](#54-匿名生命周期)
  - [6. 常见模式](#6-常见模式)
    - [6.1 迭代器模式](#61-迭代器模式)
    - [6.2 智能指针模式](#62-智能指针模式)
    - [6.3 访问者模式](#63-访问者模式)
    - [6.4 缓存模式](#64-缓存模式)
  - [7. 错误诊断](#7-错误诊断)
    - [7.1 生命周期太短](#71-生命周期太短)
    - [7.2 生命周期不匹配](#72-生命周期不匹配)
    - [7.3 同时借用冲突](#73-同时借用冲突)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 优先使用省略](#81-优先使用省略)
    - [8.2 显式标注复杂情况](#82-显式标注复杂情况)
    - [8.3 文档说明生命周期](#83-文档说明生命周期)
    - [8.4 避免过度约束](#84-避免过度约束)
  - [总结](#总结)

---

## 1. 概念定义

### 1.1 什么是生命周期

**生命周期(Lifetime)** 是引用保持有效的**代码区域**。每个引用都有隐式或显式的生命周期，确保它不会在指向的数据被释放后使用。

```rust
{
    let x = 5;           // x的生命周期开始
    let r = &x;          // r借用x，生命周期与x关联
    println!("{}", r);   // 使用r
}                        // x和r的生命周期结束
```

### 1.2 直观理解

```
代码执行时间轴:
─────────────────────────────────────────►

let x = 5;          ──┐
                      │ 'x (x的生命周期)
let r = &x;          ──┼──┐
                      │  │ 'r (r的生命周期)
println!("{}", r);   ──┼──┘
                      │
}                   ──┘

'r ⊆ 'x  (r的生命周期必须包含在x的生命周期内)
```

### 1.3 为什么需要生命周期

**防止悬空指针**:

```rust
// 如果没有生命周期检查...
let r;              // r声明
{
    let x = 5;      // x创建
    r = &x;         // r指向x
}                   // x被释放！
println!("{}", r);   // 灾难：r指向无效内存
```

Rust编译器通过生命周期分析拒绝这段代码。

---

## 2. 形式化理论

### 2.1 生命周期作为区域

**定义 2.1** (生命周期):

```
'a ⊆ ProgramPoints

生命周期是程序控制流图(CFG)中的点集。
```

**定义 2.2** (存活集):

```
Live(p) = {x | 变量x在程序点p是存活的}

x ∈ Live(p) ⟺ 存在从p到x的使用的路径，且路径上无x的重新定义
```

**定义 2.3** (引用的有效性):

```
对于引用r = &x，生命周期'a满足：
∀p ∈ 'a. x ∈ Live(p)
```

### 2.2 子类型关系

**定义 2.4** (生命周期包含):

```
'a: 'b  ⟺  'b ⊆ 'a

读作："'a 包含 'b" 或 "'a 至少和 'b 一样长"
```

**图示**:

```
'a (较长)    ┌─────────────────────┐
'b (较短)        ┌───────────┐
                  └───────────┘
            └─────────────────────┘
```

### 2.3 借用检查的形式化

**规则 2.5** (借用有效性):

```
Γ ⊢ &x : &'a T
─────────────────
Γ ⊢ x : T
∀p ∈ 'a. x ∈ Live(p)
```

**规则 2.6** (可变借用独占性):

```
Γ ⊢ &mut x : &'a mut T
────────────────────────
Γ ⊢ x : T
∀p ∈ 'a. ¬∃r ≠ &mut x. r借用x
```

---

## 3. 生命周期标注

### 3.1 显式标注语法

```rust
// 函数签名中的生命周期
fn foo<'a, 'b>(x: &'a str, y: &'b str) -> &'a str
//    │   │     │         │          └── 返回值生命周期
//    │   │     │         └── y的生命周期
//    │   │     └── x的生命周期
//    │   └── 第二个生命周期参数
//    └── 第一个生命周期参数
```

### 3.2 典型标注模式

**模式1: 输入输出相同**

```rust
fn identity<'a>(x: &'a i32) -> &'a i32 {
    x
}
```

**模式2: 多个输入，选择最短**

```rust
fn min_lifetime<'a, 'b>(x: &'a str, y: &'b str) -> &'a str
where
    'b: 'a,  // 'b必须至少和'a一样长
{
    if x.len() < y.len() { x } else { y }
}
```

**模式3: 返回独立生命周期**

```rust
struct Pair<'a, 'b> {
    first: &'a str,
    second: &'b str,
}

impl<'a, 'b> Pair<'a, 'b> {
    fn first(&self) -> &'a str { self.first }
    fn second(&self) -> &'b str { self.second }
}
```

### 3.3 结构体生命周期

```rust
// 引用字段必须有显式生命周期
struct Person<'a> {
    name: &'a str,      // 借用外部字符串
    age: u32,           // 拥有值
}

// 多个独立生命周期
struct Document<'a, 'b> {
    title: &'a str,
    content: &'b str,
}

// 自引用结构（复杂情况）
struct Parser<'a> {
    text: &'a str,
    pos: usize,
    // current: &'a str,  // 可能指向text内部
}
```

### 3.4 Trait对象生命周期

```rust
// Trait对象有默认生命周期
fn draw(obj: &dyn Drawable)  // 等价于 &'_ dyn Drawable

// 显式标注
trait Parser<'input> {
    fn parse(&self, input: &'input str) -> Result<&'input str, Error>;
}
```

---

## 4. 省略规则

### 4.1 生命周期省略规则

Rust编译器自动推断生命周期，遵循三条规则：

**规则1**: 每个输入引用获得独立生命周期参数

```rust
fn foo(x: &i32, y: &str)      // 等价于
fn foo<'a, 'b>(x: &'a i32, y: &'b str)
```

**规则2**: 如果只有一个输入生命周期，它分配给所有输出

```rust
fn first(x: &[i32]) -> &i32   // 等价于
fn first<'a>(x: &'a [i32]) -> &'a i32
```

**规则3**: 如果有`&self`或`&mut self`，其生命周期分配给所有输出

```rust
impl Person {
    fn name(&self) -> &str      // 等价于
    fn name<'a>(&'a self) -> &'a str
}
```

### 4.2 无法省略的情况

```rust
// 多个输入，无法确定输出生命周期
fn longest(x: &str, y: &str) -> &str  // 错误！必须显式标注

// 正确标注
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str
```

### 4.3 方法中的生命周期

```rust
struct Buffer<'a> {
    data: &'a [u8],
}

impl<'a> Buffer<'a> {
    // 使用self的生命周期
    fn data(&self) -> &'a [u8] {
        self.data
    }

    // 不同生命周期
    fn find(&self, pat: &[u8]) -> Option<&'a [u8]> {
        // pat有自己的生命周期，返回值使用'a
        // ...
    }
}
```

---

## 5. 高级特性

### 5.1 NLL (Non-Lexical Lifetimes)

Rust 2018+ 引入NLL，生命周期在**最后使用处**结束。

```rust
let mut x = vec![1, 2, 3];

let y = &x[0];          // ──┐
println!("{}", y);      //    │ y的生命周期
                        // ───┘ 在这里结束（NLL）

x.push(4);              // OK! x的可变借用从这里开始
```

**传统词法生命周期 vs NLL**:

```
词法生命周期:
let y = &x;     ──┐
}                   │ y的生命周期
x.push(4);      ────┘ 错误！y仍然存在

NLL:
let y = &x;     ──┐
use(y);             │ y的生命周期
x.push(4);      ────┘ OK！y已不再使用
```

### 5.2 生命周期约束

**where子句约束**:

```rust
fn longest<'a, 'b, 'out>(x: &'a str, y: &'b str) -> &'out str
where
    'a: 'out,  // 'a包含'out（'a至少和'out一样长）
    'b: 'out,  // 'b包含'out
{
    if x.len() > y.len() { x } else { y }
}
```

**复合约束**:

```rust
trait Processor<'input, 'output>
where
    'input: 'output,
{
    fn process(&self, input: &'input str) -> &'output str;
}
```

### 5.3 Higher-Ranked Trait Bounds (HRTB)

```rust
// 对所有'a都适用的函数指针
fn with_closure<F>(f: F)
where
    F: for<'a> Fn(&'a str) -> &'a str,
{
    let s = String::from("hello");
    f(&s);
}

// 等价于高阶类型: ∀'a. (&'a str) -> &'a str
```

### 5.4 匿名生命周期

Rust 2021+ 引入匿名生命周期 `'_`:

```rust
// 显式匿名生命周期
fn foo(x: &'_ i32) -> &'_ i32

// 结构体中的匿名生命周期
struct Foo<'a> {
    bar: &'_ str,  // 使用'a
}

// impl块中的匿名生命周期
impl Foo<'_> {
    fn method(&self) -> &'_ str {  // 使用self的生命周期
        self.bar
    }
}
```

---

## 6. 常见模式

### 6.1 迭代器模式

```rust
struct Iter<'a, T> {
    data: &'a [T],
    pos: usize,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.data.get(self.pos)?;
        self.pos += 1;
        Some(item)
    }
}
```

### 6.2 智能指针模式

```rust
struct Ref<'a, T> {
    value: &'a T,
}

impl<'a, T> Deref for Ref<'a, T> {
    type Target = T;
    fn deref(&self) -> &T { self.value }
}

impl<'a, T> Clone for Ref<'a, T> {
    fn clone(&self) -> Self { *self }  // Copy语义
}

impl<'a, T> Copy for Ref<'a, T> {}
```

### 6.3 访问者模式

```rust
trait Visitor<'ast> {
    fn visit_expr(&mut self, expr: &'ast Expr);
    fn visit_stmt(&mut self, stmt: &'ast Stmt);
}

struct Ast<'a> {
    stmts: Vec<&'a Stmt<'a>>,
}
```

### 6.4 缓存模式

```rust
struct Cache<'k, 'v, K, V> {
    data: HashMap<&'k K, &'v V>,
}

impl<'k, 'v, K: Eq + Hash, V> Cache<'k, 'v, K, V> {
    fn get(&self, key: &'k K) -> Option<&&'v V> {
        self.data.get(key)
    }
}
```

---

## 7. 错误诊断

### 7.1 生命周期太短

```rust
fn bad() -> &String {
    let s = String::from("x");
    &s  // 错误：s的生命周期太短
}
```

**错误信息**:

```
error: `s` does not live long enough
```

**解决**: 返回所有权

```rust
fn good() -> String {
    String::from("x")
}
```

### 7.2 生命周期不匹配

```rust
fn longest<'a>(x: &'a str, y: &str) -> &'a str {
    if x.len() > 2 { x } else { y }  // 错误：y可能不够长
}
```

**解决**: 统一生命周期

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str
```

### 7.3 同时借用冲突

```rust
let mut data = vec![1, 2, 3];
let first = &data[0];
data.push(4);  // 错误：已有不可变借用
println!("{}", first);
```

**解决**: 分离借用

```rust
let mut data = vec![1, 2, 3];
{
    let first = &data[0];
    println!("{}", first);
}
data.push(4);
```

---

## 8. 最佳实践

### 8.1 优先使用省略

```rust
// 好的：使用省略规则
fn first(items: &[i32]) -> Option<&i32>

// 不必要的显式标注
fn first_explicit<'a>(items: &'a [i32]) -> Option<&'a i32>
```

### 8.2 显式标注复杂情况

```rust
// 好的：多个输入需要明确关系
fn merge<'a, 'b>(a: &'a [u8], b: &'b [u8]) -> Merged<'a, 'b>

// 好的：返回类型包含引用
fn parse<'input>(input: &'input str) -> ParseResult<'input>
```

### 8.3 文档说明生命周期

```rust
/// 返回输入字符串中最长的行
///
/// # 生命周期
/// - 返回值的生命周期与输入相同
/// - 返回的切片指向输入数据的内部
fn longest_line(content: &str) -> &str {
    // ...
}
```

### 8.4 避免过度约束

```rust
// 过于约束：要求两个输入生命周期相同
fn overly_constrained<'a>(x: &'a str, y: &'a str) -> &'a str

// 更灵活：独立生命周期
fn flexible<'a, 'b>(x: &'a str, y: &'b str) -> &'a str
```

---

## 总结

生命周期是Rust编译时 borrow checker 的核心机制：

1. **安全**: 编译期防止悬空指针
2. **零成本**: 运行时不产生开销
3. **表达**: 支持复杂数据结构
4. **灵活**: NLL减少不必要的约束

掌握生命周期是写出高效、安全Rust代码的关键。
