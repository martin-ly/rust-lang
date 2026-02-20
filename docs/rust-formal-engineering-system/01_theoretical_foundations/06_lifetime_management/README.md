# 生命周期管理理论

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> 内容已整合至： [lifetime_formalization.md](../../../research_notes/formal_methods/lifetime_formalization.md)

[返回主索引](../../00_master_index.md)

---

## 形式化链接

| 文档 | 路径 | 内容 |
| :--- | :--- | :--- |
| **生命周期形式化** | [../../../research_notes/formal_methods/lifetime_formalization.md](../../../research_notes/formal_methods/lifetime_formalization.md) | 区域理论、生命周期约束 |
| **型变理论** | [../../../research_notes/type_theory/variance_theory.md](../../../research_notes/type_theory/variance_theory.md) | 生命周期与子类型关系 |
| **借用检查器证明** | [../../../research_notes/formal_methods/borrow_checker_proof.md](../../../research_notes/formal_methods/borrow_checker_proof.md) | 生命周期验证的形式化 |
| **证明索引** | [../../../research_notes/PROOF_INDEX.md](../../../research_notes/PROOF_INDEX.md) | 生命周期相关证明 |
| **工具指南** | [../../../research_notes/TOOLS_GUIDE.md](../../../research_notes/TOOLS_GUIDE.md) | 生命周期验证工具 |

---

## 生命周期的形式化模型

### 生命周期作为区域（Region）

生命周期可以形式化为程序执行中的时间区域：

```rust
// 生命周期 'a 表示程序执行的一个区域
// 'static 是最长的生命周期（整个程序执行期间）

// 显式生命周期标注
struct StringHolder<'a> {
    // s 的生命周期至少与结构体一样长
    s: &'a str,
}

impl<'a> StringHolder<'a> {
    fn new(s: &'a str) -> Self {
        Self { s }
    }

    fn get(&self) -> &'a str {
        self.s
    }
}

// 生命周期约束：'b: 'a 表示 'b 至少和 'a 一样长
fn constrained_lifetime<'a, 'b: 'a>(
    short: &'a str,
    long: &'b str
) -> &'a str {
    // 可以返回 short，因为 'a ⊆ 'b
    short
}
```

### 生命周期省略规则（Lifetime Elision）

```rust
// Rust 自动推导生命周期的规则

// 规则 1：每个引用参数获得独立的生命周期
// fn foo<'a>(x: &'a str)

// 规则 2：只有一个输入生命周期时，它分配给所有输出
// fn foo<'a>(x: &'a str) -> &'a str

// 规则 3：多个输入生命周期但有 &self 或 &mut self 时，self 的生命周期分配给输出
// impl<'a> Foo<'a> {
//     fn bar(&'b self, x: &'c str) -> &'b str
// }

// 示例：自动推导
fn first_word(s: &str) -> &str {  // 等价于 fn first_word<'a>(s: &'a str) -> &'a str
    s.split_whitespace().next().unwrap_or(s)
}

// 示例：需要显式标注的情况
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

### 生命周期边界与类型

```rust
// 边界生命周期：'static
// 表示数据存活于整个程序执行期间

fn static_lifetime() {
    // 字符串字面量是 'static
    let s: &'static str = "hello";

    // 静态变量
    static COUNTER: i32 = 0;
    let r: &'static i32 = &COUNTER;

    // Box::leak 可以创建 'static 引用
    let boxed = Box::new(vec![1, 2, 3]);
    let leaked: &'static [i32] = Box::leak(boxed);
}

// Trait 对象的生命周期
fn trait_object_lifetime() {
    // dyn Trait 有隐式的 'static 生命周期
    let obj: Box<dyn std::fmt::Display> = Box::new(42);

    // 显式标注生命周期
    let s = String::from("hello");
    let obj: Box<dyn std::fmt::Display + '_> = Box::new(&s);
}
```

### 高级生命周期模式

```rust
// 生命周期与泛型结合
struct Parser<'input, T> {
    input: &'input str,
    _phantom: std::marker::PhantomData<T>,
}

impl<'input, T> Parser<'input, T> {
    fn new(input: &'input str) -> Self {
        Self {
            input,
            _phantom: std::marker::PhantomData,
        }
    }
}

// 生命周期边界约束
fn bounded_lifetime<'a, T>()
where
    T: 'a,  // T 的所有引用必须至少存活 'a
{
}

// 复杂生命周期示例：自引用结构
use std::pin::Pin;

struct SelfReferential<'a> {
    data: String,
    // ptr 指向 data 内部的某个位置
    ptr: &'a str,
}

// 使用 Pin 确保自引用结构不会被移动
fn self_referential_demo() {
    let data = String::from("hello world");
    let ptr = &data[..5];  // 指向 "hello"

    let s = SelfReferential { data, ptr };
    // 现在 s 不能安全地移动，因为 ptr 指向 data
}
```

### 生命周期的子类型关系

```rust
// 协变（Covariance）：保持子类型方向
// &'a T 对于 'a 是协变的：如果 'b: 'a，那么 &'b T <: &'a T

fn covariance<'a>(x: &'a str) {
    // 在函数体内，我们可以认为 x 的生命周期是 'a
    println!("{}", x);
}

fn covariance_demo() {
    let long_lived = String::from("hello");
    {
        let short_lived = &long_lived;
        // short_lived: &'short str
        // 可以传递给期望 &'a str 的函数，其中 'a 是 'short 的超集
        covariance(short_lived);  // 协变转换
    }
}

// 逆变（Contravariant）：反转子类型方向
// fn(T) -> U 对于 T 是逆变的

fn contravariance<F>(f: F)
where
    F: Fn(&'static str),
{
    let s: &str = "hello";  // 非 'static 生命周期
    f(s);  // 可以接受，因为 fn(&'static str) <: fn(&'short str)
}

// 不变（Invariant）：无子类型关系
// &mut T 对于 T 是不变的

fn invariance(x: &mut &'static str) {
    // x: &mut &'static str
    // 不能传入 &mut &'short str
}
```
