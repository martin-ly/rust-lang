# 编译器错误码 → 本项目文档映射

> **创建日期**: 2026-02-13
> **最后更新**: 2026-02-13
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 常见 Rust 编译器错误码快速定位到本项目文档与示例
> **权威源**: [Compiler Error Index](https://doc.rust-lang.org/error-index.html)

---

## 快速查找

遇到编译错误时，根据错误码（如 `E0382`）在下表查找本项目对应文档。

---

## 所有权与借用 (E03xx)

| 错误码 | 典型信息 | 本项目文档 | 速查卡 |
| :--- | :--- | :--- | :--- || **E0382** | borrow of moved value | [TROUBLESHOOTING 所有权错误](../05_guides/TROUBLESHOOTING_GUIDE.md#1-所有权错误) | [ownership_cheatsheet](quick_reference/ownership_cheatsheet.md) |
| **E0383** | partial move / borrow of partially moved value | C01 所有权、[EDGE_CASES](./EDGE_CASES_AND_SPECIAL_CASES.md) | ownership_cheatsheet |
| **E0384** | cannot assign twice to immutable variable | C03 控制流 | control_flow_functions_cheatsheet |
| **E0499** | cannot borrow as mutable more than once | C01 借用检查器 | ownership_cheatsheet |
| **E0502** | cannot borrow as immutable (already borrowed as mutable) | C01 借用规则 | ownership_cheatsheet |
| **E0503** | cannot use (value was moved) | C01 所有权 | ownership_cheatsheet |
| **E0505** | cannot move out of (value is borrowed) | C01 借用与移动 | ownership_cheatsheet |
| **E0506** | cannot assign to (borrowed) | C01 借用 | ownership_cheatsheet |
| **E0507** | cannot move out of borrowed content | C01 借用检查器 | ownership_cheatsheet |

---

## 生命周期 (E05xx)

| 错误码 | 典型信息 | 本项目文档 | 速查卡 |
| :--- | :--- | :--- | :--- || **E0597** | does not live long enough | [TROUBLESHOOTING 生命周期](../05_guides/TROUBLESHOOTING_GUIDE.md#2-生命周期错误) | [type_system](quick_reference/type_system.md) |
| **E0599** | no method named ... for type | C02 Trait、C04 泛型 | type_system、generics_cheatsheet |
| **E0609** | no field ... on type | C02 结构体、C03 枚举 | type_system |
| **E0614** | expected ... found ... (type mismatch) | C02 类型系统 | type_system |

---

## 类型系统 (E02xx, E03xx)

| 错误码 | 典型信息 | 本项目文档 | 速查卡 |
| :--- | :--- | :--- | :--- || **E0308** | mismatched types | [TROUBLESHOOTING 类型不匹配](../05_guides/TROUBLESHOOTING_GUIDE.md#3-类型不匹配) | type_system |
| **E0277** | trait bound not satisfied | C02 Trait、C04 泛型约束 | generics_cheatsheet |
| **E0282** | type annotations needed | C02 类型推断 | type_system |
| **E0283** | type annotations required | C02 类型推断 | type_system |
| **E0284** | type ... cannot be formatted | C03 格式化 | strings_formatting_cheatsheet |
| **E0310** | parameter ... may not live long enough | C01 生命周期 | type_system |
| **E0325** | overflow evaluating requirement | C04 泛型、GATs | generics_cheatsheet |

---

## 错误处理 (E0xxx)

| 错误码 | 典型信息 | 本项目文档 | 速查卡 |
| :--- | :--- | :--- | :--- || **E0433** | unresolved import | C02 模块系统 | modules_cheatsheet |
| **E0446** | private type in public interface | C02 可见性 | modules_cheatsheet |
| **E0451** | unknown attribute | C11 宏、属性 | macros_cheatsheet |
| **E0463** | can't find crate | Cargo 依赖 | cargo_cheatsheet |

---

## 异步与并发 (E0xxx)

| 错误码 | 典型信息 | 本项目文档 | 速查卡 |
| :--- | :--- | :--- | :--- || **E0373** | closure may outlive current function | C06 异步、C01 生命周期 | [async_patterns](quick_reference/async_patterns.md) |
| **E0378** | Send/Sync 相关 | C05 线程、C06 异步 | threads_concurrency_cheatsheet |
| **E0381** | borrow of moved value in async | C06 异步、持锁跨 await | async_patterns |

---

## 宏与属性 (E0xxx)

| 错误码 | 典型信息 | 本项目文档 | 速查卡 |
| :--- | :--- | :--- | :--- || **E0658** | unstable feature | 06_toolchain、Edition | - |
| **E0554** | unknown feature | Cargo features | cargo_cheatsheet |

---

## 错误码详细代码示例与修复

### E0382 - borrow of moved value

**错误代码示例**:

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 的所有权转移到 s2

    // ❌ 编译错误：value borrowed here after move
    println!("{}", s1);
}
```

**修复方案**:

```rust
// 方案 1: 使用引用（借用）
fn main() {
    let s1 = String::from("hello");
    let s2 = &s1;  // 借用 s1，不转移所有权

    println!("{} {}", s1, s2);  // ✅ 两者都可用
}

// 方案 2: 克隆（如果类型实现了 Clone）
fn main() {
    let s1 = String::from("hello");
    let s2 = s1.clone();  // 深度复制

    println!("{} {}", s1, s2);  // ✅ 两者都可用
}

// 方案 3: 如果只需要 s2，直接使用 s2
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // 转移所有权

    println!("{}", s2);  // ✅ 使用 s2
    // 不再需要 s1
}
```

**形式化解释**:

- 违反规则: [规则 2 - 移动语义](../research_notes/formal_methods/ownership_model.md#规则-2-移动语义)
- 形式化: $\text{move}(x, y) \rightarrow \Omega(x) = \text{Moved} \land \Omega(y) = \text{Owned}$
- 后果: 使用已移动的值违反所有权唯一性 ([定理 2](../research_notes/formal_methods/ownership_model.md#定理-2-所有权唯一性))

---

### E0499 - cannot borrow as mutable more than once

**错误代码示例**:

```rust
fn main() {
    let mut s = String::from("hello");

    let r1 = &mut s;
    let r2 = &mut s;  // ❌ 编译错误：cannot borrow as mutable more than once

    println!("{} {}", r1, r2);
}
```

**修复方案**:

```rust
// 方案 1: 限制借用作用域
fn main() {
    let mut s = String::from("hello");

    {
        let r1 = &mut s;
        println!("{}", r1);
    }  // r1 在这里结束

    let r2 = &mut s;  // ✅ 现在可以新的可变借用
    println!("{}", r2);
}

// 方案 2: 按顺序使用
fn main() {
    let mut s = String::from("hello");

    let r1 = &mut s;
    r1.push_str(" world");
    // r1 不再使用，隐式结束

    let r2 = &mut s;  // ✅ NLL 允许，因为 r1 不再使用
    println!("{}", r2);
}

// 方案 3: 如果确实需要同时访问，重新设计数据结构
use std::mem::take;

fn main() {
    let mut s = String::from("hello");
    let taken = take(&mut s);  // 取出所有权
    s = process(taken);        // 处理后再放回去
}

fn process(s: String) -> String {
    s + " processed"
}
```

**形式化解释**:

- 违反规则: [规则 1 - 可变借用唯一性](../research_notes/formal_methods/borrow_checker_proof.md#规则-1唯一性)
- 形式化: $\forall b_1, b_2: \text{type}(b_1) = \&mut T \land \text{target}(b_1) = \text{target}(b_2) \rightarrow b_1 = b_2$
- 目的: 保证数据竞争自由 ([定理 1](../research_notes/formal_methods/borrow_checker_proof.md#定理-1-数据竞争自由))

---

### E0502 - cannot borrow as immutable because it is borrowed as mutable

**错误代码示例**:

```rust
fn main() {
    let mut s = String::from("hello");

    let r1 = &mut s;
    let r2 = &s;  // ❌ 编译错误：cannot borrow as immutable

    println!("{} {}", r1, r2);
}
```

**修复方案**:

```rust
// 方案 1: 先使用不可变借用，再使用可变借用
fn main() {
    let mut s = String::from("hello");

    let r1 = &s;
    println!("读取: {}", r1);
    // r1 不再使用

    let r2 = &mut s;  // ✅ 现在可以可变借用
    r2.push_str(" world");
    println!("修改后: {}", r2);
}

// 方案 2: 使用作用域隔离
fn main() {
    let mut s = String::from("hello");

    {
        let r1 = &s;
        println!("读取: {}", r1);
    }  // 不可变借用结束

    {
        let r2 = &mut s;
        r2.push_str(" world");
        println!("修改后: {}", r2);
    }  // 可变借用结束
}
```

**形式化解释**:

- 违反规则: [规则 2 - 可变与不可变互斥](../research_notes/formal_methods/borrow_checker_proof.md#规则-2共享性)
- 目的: 防止读写数据竞争 ([定理 1](../research_notes/formal_methods/borrow_checker_proof.md#定理-1-数据竞争自由))

---

### E0597 - does not live long enough

**错误代码示例**:

```rust
fn main() {
    let r;
    {
        let s = String::from("hello");
        r = &s;  // ❌ 编译错误：s does not live long enough
    }  // s 在这里被丢弃
    println!("{}", r);  // r 引用已释放的内存
}
```

**修复方案**:

```rust
// 方案 1: 确保引用不超过被引用者的生命周期
fn main() {
    let s = String::from("hello");
    let r = &s;  // ✅ r 的生命周期在 s 之内

    println!("{}", r);
}  // s 和 r 一起结束

// 方案 2: 使用返回值传递所有权
fn get_string() -> String {
    String::from("hello")
}

fn main() {
    let s = get_string();  // 获得所有权
    println!("{}", s);
}

// 方案 3: 使用 'static 生命周期的字符串
fn main() {
    let r: &'static str = "hello";  // 字符串字面量生命周期为 'static
    println!("{}", r);
}
```

**形式化解释**:

- 违反规则: [规则 3 - 借用有效性](../research_notes/formal_methods/borrow_checker_proof.md#规则-3有效性)
- 形式化: $\text{Valid}(b) \leftrightarrow \text{Lifetime}(b) \subseteq \text{Scope}(b)$
- 目的: 防止悬垂引用 ([定理 LF-T2](../research_notes/formal_methods/lifetime_formalization.md#定理-lf-t2引用有效性))

---

### E0308 - mismatched types

**错误代码示例**:

```rust
fn main() {
    let x: i32 = "hello";  // ❌ 编译错误：expected i32, found &str
}
```

**修复方案**:

```rust
// 方案 1: 正确的类型声明
fn main() {
    let x: &str = "hello";  // ✅ 类型匹配
}

// 方案 2: 类型转换
fn main() {
    let s = "42";
    let x: i32 = s.parse().unwrap();  // ✅ 显式解析转换
}

// 方案 3: 类型推断
fn main() {
    let x = "hello";  // ✅ 编译器自动推断为 &str
}
```

**形式化解释**:

- 类型系统保证: $\Gamma \vdash e : \tau$ ([类型推导](../research_notes/type_theory/type_system_foundations.md))
- 子类型关系: $\tau_1 <: \tau_2$ 允许协变位置替换

---

### E0277 - trait bound not satisfied

**错误代码示例**:

```rust
fn print_it<T>(x: T) {
    // ❌ 编译错误：T doesn't implement Display
    println!("{}", x);
}
```

**修复方案**:

```rust
use std::fmt::Display;

// 方案 1: 添加 Trait Bound
fn print_it<T: Display>(x: T) {
    println!("{}", x);  // ✅ T 实现了 Display
}

// 方案 2: 使用 where 从句
fn print_it<T>(x: T)
where
    T: Display,
{
    println!("{}", x);
}

// 方案 3: 为自定义类型实现 Trait
struct Point { x: i32, y: i32 }

impl Display for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {})", self.x, self.y)
    }
}

fn main() {
    print_it(Point { x: 1, y: 2 });  // ✅ 可以打印了
}
```

**形式化解释**:

- Trait 约束: $\Gamma \vdash T: \text{Trait}$ ([Trait 系统](../research_notes/formal_methods/ownership_model.md))
- 多态约束: $\forall T. T: \text{Display} \rightarrow \text{can\_format}(T)$

---

### E0373 - closure may outlive current function

**错误代码示例**:

```rust
fn make_closure() -> Box<dyn Fn() -> i32> {
    let x = 42;
    // ❌ 编译错误：closure may outlive current function
    Box::new(move || x)  // x 是局部变量
}
```

**修复方案**:

```rust
// 方案 1: 使用 move 关键字转移所有权
fn make_closure() -> impl FnOnce() -> i32 {
    let x = 42;
    move || x  // ✅ 将 x 的所有权移入闭包
}

// 方案 2: 如果需要在多次调用中使用，使用 Arc
use std::sync::Arc;

fn make_closure_shared() -> impl Fn() -> i32 {
    let x = Arc::new(42);
    let x_clone = Arc::clone(&x);
    move || *x_clone  // ✅ Arc 可以安全共享
}

// 方案 3: 使用 'static 数据
fn make_closure_static() -> impl Fn() -> i32 {
    let x: i32 = 42;  // i32 实现 Copy
    move || x  // ✅ 复制而非移动
}
```

**形式化解释**:

- 生命周期约束: $\text{lft}(\text{closure}) \subseteq \text{lft}(\text{captured\_vars})$
- 违反规则: [规则 3 - 借用有效性](../research_notes/formal_methods/borrow_checker_proof.md#规则-3有效性)

---

## 错误码快速修复索引

| 错误码 | 常见原因 | 快速修复 | 形式化规则 |
| :--- | :--- | :--- | :--- |
| **E0382** | 使用已移动的值 | 使用引用或 `.clone()` | 规则 2 - 移动语义 |
| **E0499** | 双重可变借用 | 使用作用域隔离或 NLL | 规则 1 - 可变借用唯一性 |
| **E0502** | 可变与不可变共存 | 分离借用作用域 | 规则 2 - 互斥借用 |
| **E0597** | 生命周期不足 | 确保引用在有效期内 | 规则 3 - 借用有效性 |
| **E0308** | 类型不匹配 | 类型转换或修正声明 | 类型系统一致性 |
| **E0277** | Trait 未实现 | 添加 Trait Bound 或实现 Trait | Trait 约束 |
| **E0373** | 闭包生命周期 | 使用 `move` 或 `Arc` | 捕获变量生命周期 |

---

## 使用建议

1. **编译错误**：复制完整错误信息，提取 `error[EXXXX]` 中的错误码
2. **查表**：在本文档中查找对应错误码
3. **跳转**：点击「本项目文档」或「速查卡」链接深入学习
4. **官方详解**：访问 [Compiler Error Index](https://doc.rust-lang.org/error-index.html) 查看完整说明

---

## 相关文档

### 故障排查

- [故障排查指南](../05_guides/TROUBLESHOOTING_GUIDE.md)
- [边界条件与特例](./EDGE_CASES_AND_SPECIAL_CASES.md)
- [速查卡目录](quick_reference/README.md)

### 形式化基础

- [所有权模型形式化](../research_notes/formal_methods/ownership_model.md)
- [借用检查器证明](../research_notes/formal_methods/borrow_checker_proof.md)
- [生命周期形式化](../research_notes/formal_methods/lifetime_formalization.md)

### 官方资源

- [官方 Compiler Error Index](https://doc.rust-lang.org/error-index.html)
