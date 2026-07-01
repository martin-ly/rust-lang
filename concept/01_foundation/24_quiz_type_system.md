> **内容分级**:
>
> [综述级]

# 测验：类型系统（试点扩展）
>
> **EN**: Type System
> **Summary**: Quiz Type System. Core Rust concept.
> **受众**: [初学者]
> **内容分级**: [综述级]
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链
> **后置概念**: [Ownership](23_quiz_ownership_borrowing.md)
---

> **来源**: · [自测题库](../00_meta/self_assessment.md)
> [The Rust Programming Language — Ch3 Common Programming Concepts](https://doc.rust-lang.org/book/ch03-00-common-programming-concepts.html) ·
> [The Rust Programming Language — Ch6 Enums and Pattern Matching](https://doc.rust-lang.org/book/ch06-00-enums.html) ·
> [The Rust Programming Language — Ch18 Patterns](https://doc.rust-lang.org/book/ch18-00-patterns.html)
>
> **前置概念**:
> [Type System](04_type_system.md) ·
> [Collections](08_collections.md) ·
> [Strings and Text](09_strings_and_text.md)
>
> **对应练习**:
> [`exercises/src/type_system/`](../../exercises/src/type_system)

---

> **Bloom 层级**: 理解 → 应用
> **定位**: 嵌入式互动测验扩展——验证 L1 类型系统（Type System）核心概念（标量/复合类型、enum、模式匹配（Pattern Matching）、类型转换）的掌握程度。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

## 一、标量与复合类型

### Q1. 以下代码的输出是什么？

```rust
fn main() {
    let x: u8 = 255;
    let y = x.wrapping_add(1);
    println!("{y}");
}
```
<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：`0`

**解析**：`u8` 范围为 0–255。`255 + 1` 在数学上溢出，但 `.wrapping_add()` 执行**环绕运算**（wrap around），结果回到 0。

**对比**：

| 方法 | 行为 | 溢出 255+1 时 |
|:---|:---|:---|
| `+` | debug 模式 panic，release 环绕 | panic（debug）/ 0（release） |
| `.wrapping_add(n)` | 始终环绕 | 0 |
| `.saturating_add(n)` | 饱和截断 | 255 |
| `.checked_add(n)` | 返回 `Option` | `None` |
| `.overflowing_add(n)` | 返回 (结果, 是否溢出) | `(0, true)` |

**知识点**：Rust 数值运算提供多种溢出处理策略，默认行为在 debug/release 间不一致是常见陷阱。[→ 数值类型详解](10_numerics.md)

</details>

---

### Q2. 以下代码能否编译？

```rust
fn main() {
    let tup = (500, 6.4, 1);
    let (x, y, z) = tup;
    println!("{y}");
}
```
<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出 `6.4`

**解析**：Rust 支持**元组解构（Tuple Destructuring）**。`(x, y, z) = tup` 将元组的三个元素分别绑定到 `x`、`y`、`z`。

**元组特性**：

- 固定长度，类型可异构 `(i32, f64, u8)`
- 通过索引访问：`tup.0`、`tup.1`
- 空元组 `()` 是单元类型（unit type），表示"无返回值"

**知识点**：元组是 Rust 中最轻量的"匿名结构体（Struct）"，广泛用于函数多返回值。→ 类型系统（Type System）详解

</details>

---

### Q3. 以下代码能否编译？若不能，如何修改？

```rust,ignore
fn main() {
    let a = [1, 2, 3, 4, 5];
    let index = 10;
    let element = a[index];
    println!("{element}");
}
```
<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`index out of bounds: the length is 5 but the index is 10`

**解析**：Rust 在**编译期**（若索引为常量）或**运行期**检查数组越界。与 C/C++ 不同，Rust 绝不允许缓冲区溢出访问。

**修改方案**：

```rust,ignore
let element = a.get(index); // 返回 Option<&T>
match element {
    Some(val) => println!("{val}"),
    None => println!("Index out of bounds"),
}
```
**知识点**：`[]` 索引访问在越界时 panic，`.get()` 返回 `Option` 提供安全替代。[→ 集合类型详解](08_collections.md)

</details>

---

## 二、枚举与模式匹配

### Q4. 以下代码的输出是什么？

```rust
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(i32, i32, i32),
}

fn main() {
    let msg = Message::Move { x: 10, y: 20 };
    match msg {
        Message::Quit => println!("Quit"),
        Message::Move { x, y } => println!("Move to {x}, {y}"),
        Message::Write(text) => println!("Write: {text}"),
        Message::ChangeColor(r, g, b) => println!("RGB({r},{g},{b})"),
    }
}
```
<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：`Move to 10, 20`

**解析**：`match` 表达式对 `Message::Move { x: 10, y: 20 }` 进行模式匹配（Pattern Matching），第二个 arm 匹配成功，解构出 `x = 10`、`y = 20`。

**Rust enum 的强大之处**：

- 每个变体可携带**不同类型和数量**的数据
- `Quit`（无数据）、`Move { x, y }`（匿名结构体（Struct））、`Write(String)`（单个值）、`ChangeColor(i32, i32, i32)`（元组）
- 对比 C/Java 的 enum：Rust enum 是**代数数据类型（ADT）**，远不止是常量标签

**知识点**：Rust 的 enum + match 组合是语言核心特性，替代了其他语言中的 nullable 类型、union 和异常。[→ 枚举详解](04_type_system.md)

</details>

---

### Q5. 以下代码能否编译？解释 `if let` 的作用

```rust
enum Option<T> {
    Some(T),
    None,
}

fn main() {
    let some_number = Some(5);
    if let Some(x) = some_number {
        println!("Value: {x}");
    } else {
        println!("No value");
    }
}
```
<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译（注：代码中重定义了 `Option`，实际应使用 `std::option::Option`）

**解析**：`if let` 是 `match` 的**语法糖**，用于只关心一个模式的情况：

```rust,ignore
// 以下两者等价：
if let Some(x) = some_number { ... }

match some_number {
    Some(x) => { ... }
    _ => {} // 忽略其他所有情况
}
```
**使用场景**：

- 只匹配一个模式，其他情况统一处理
- 比完整 `match` 更简洁，避免冗余的 `_ => {}`

**相关语法**：`while let` 用于在模式匹配（Pattern Matching）成功时循环

**知识点**：`if let` / `while let` 是 Rust "**只想处理一个模式**"场景下的惯用写法。[→ 模式匹配（Pattern Matching）详解](04_type_system.md)

</details>

---

### Q6. 以下代码的输出是什么？解释 `_` 和 `..` 的作用

```rust
fn main() {
    let point = (3, 5, 7);
    match point {
        (0, ..) => println!("On YZ plane"),
        (.., 0) => println!("On XY plane"),
        (x, .., z) => println!("x={x}, z={z}"),
    }
}
```
<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：`x=3, z=7`

**解析**：

| 模式 | 含义 |
|:---|:---|
| `(0, ..)` | 第一个元素为 0，其余忽略 |
| `(.., 0)` | 最后一个元素为 0，其余忽略 |
| `(x, .., z)` | 捕获第一个和最后一个元素，中间忽略 |

`(3, 5, 7)` 不匹配前两个模式（第一个不是 0，最后一个不是 0），匹配第三个，捕获 `x = 3`、`z = 7`。

**注意**：`..` 只能在元组/结构体（Struct）模式中使用**一次**（不能歧义），数组切片（Slice）模式除外。

**知识点**：`_` 忽略单个值，`..` 忽略剩余部分，两者是 Rust 模式匹配（Pattern Matching）中减少 boilerplate 的关键工具。[→ 模式匹配详解](04_type_system.md)

</details>

---

## 三、类型转换与强制

### Q7. 以下代码能否编译？

```rust,compile_fail
fn main() {
    let a: u32 = 10;
    let b: u64 = a;
    println!("{b}");
}
```
<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`expected u64, found u32`

**解析**：Rust **不允许隐式数值类型转换**（即使是从小范围到大范围）。必须显式转换：

```rust,ignore
let b: u64 = a as u64; // 显式类型转换
```
**`as` 关键字的行为**：

| 转换 | 示例 | 行为 |
|:---|:---|:---|
| 数值截断 | `300_i32 as i8` | `-12`（二进制截断） |
| 浮点转整数 | `3.9_f32 as i32` | `3`（向零截断） |
| 指针转换 | `&x as *const T` | 允许 |
| 引用（Reference）转指针 | `&x as *const T as usize` | 两步转换 |

**知识点**：Rust 的"无隐式转换"原则消除了 C 家族语言中大量隐蔽的类型转换 bug。[→ 类型强制与转换详解](14_coercion_and_casting.md)

</details>

---

### Q8. 以下代码能否编译？`&str` 和 `String` 的区别是什么？

```rust
fn main() {
    let s1: &str = "hello";
    let s2: String = String::from("world");
    let s3 = s1.to_string();
    let s4 = &s2;
    println!("{s3} {s4}");
}
```
<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出 `hello world`

**解析**：

| 类型 | 存储位置 | 大小 | 是否可变 | 说明 |
|:---|:---|:---:|:---:|:---|
| `&str` | 指向字符串字面量或 `String` 的切片 | 固定（指针+长度） | ❌ | 字符串切片（String Slice），不可变引用（Immutable Reference） |
| `String` | 堆分配 | 动态增长 | ✅ | 拥有所有权（Ownership）的可变字符串 |

**转换关系**：

- `String` → `&str`：自动强制（deref coercion）或显式 `&s`
- `&str` → `String`：`.to_string()` 或 `String::from(s)`

**常见陷阱**：

```rust
let s = "hello".to_string(); // ✅ 创建 String
let s: &str = "hello";       // ✅ 字符串切片
let s = "hello";              // ✅ 类型推断为 &str
```
**知识点**：`&str` 是"借用（Borrowing）"，`String` 是"拥有"。Rust 字符串设计的核心是明确所有权（Ownership）边界。→ 字符串详解

</details>

---

## 四、综合应用

### Q9. 以下代码的输出是什么？

```rust
fn main() {
    let v = vec![1, 2, 3];
    let mut iter = v.iter();
    println!("{:?}", iter.next());
    println!("{:?}", iter.next());
    println!("{:?}", iter.next());
    println!("{:?}", iter.next());
}
```
<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

```
Some(1)
Some(2)
Some(3)
None
```
**解析**：`.iter()` 创建对 `Vec` 的不可变迭代器（Iterator）。每次 `.next()` 返回 `Option<&T>`：

| 调用 | 返回值 | 说明 |
|:---|:---|:---|
| 第 1 次 | `Some(1)` | 指向第一个元素的引用（Reference） |
| 第 2 次 | `Some(2)` | 指向第二个元素的引用（Reference） |
| 第 3 次 | `Some(3)` | 指向第三个元素的引用（Reference） |
| 第 4 次 | `None` | 迭代器（Iterator）已耗尽 |

**注意**：`v.iter()` 不消耗 `v`（返回 `&T`）。若使用 `v.into_iter()`，则 `v` 被移动并消耗。

**知识点**：Iterator trait 是 Rust 标准库的核心抽象，`Option` 是处理可能缺失值的安全方式。[→ 迭代器详解](../02_intermediate/15_iterator_patterns.md)

</details>

---

### Q10. 以下代码能否编译？解释 `#[derive(Debug)]` 的作用

```rust
#[derive(Debug)]
struct Rectangle {
    width: u32,
    height: u32,
}

fn main() {
    let rect = Rectangle { width: 10, height: 20 };
    println!("{:?}", rect);
    println!("{:#?}", rect);
}
```
<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译。

**输出**：

```
Rectangle { width: 10, height: 20 }
Rectangle {
    width: 10,
    height: 20,
}
```
**解析**：

- `#[derive(Debug)]` 为结构体（Struct）**自动实现 `Debug` trait**
- `{:?}` 使用 `Debug` 格式化（紧凑单行）
- `{:#?}` 使用**美观打印（pretty-print）**格式化（多行缩进）

**可 derive 的常用 trait**：

| Trait | 功能 | 要求 |
|:---|:---|:---|
| `Debug` | 调试格式化 | 所有字段实现 `Debug` |
| `Clone` | 显式复制 | 所有字段实现 `Clone` |
| `Copy` | 隐式复制（bitwise） | 所有字段实现 `Copy` |
| `PartialEq` | 相等比较（`==`） | 所有字段实现 `PartialEq` |
| `Eq` | 全序相等 | `PartialEq` + reflexive |
| `PartialOrd` | 部分排序 | 所有字段实现 `PartialOrd` |

**知识点**：`derive` 宏（Macro）通过编译期代码生成减少 boilerplate，是 Rust 元编程的入门工具。[→ 属性与宏详解](12_attributes_and_macros.md)

</details>

---

## 五、评分参考

| 得分 | 评价 | 建议 |
|:---:|:---|:---|
| 10/10 | 🏆 类型系统（Type System）已内化 | 进阶至 L2 Trait/泛型（Generics） |
| 7–9/10 | ✅ 核心概念掌握 | 强化 [L1 类型练习](../../exercises/src/type_system)，关注错题 |
| 4–6/10 | 🔄 需巩固基础 | 重读 [Type System](04_type_system.md)，完成 rustlings 对应章节 |
| 0–3/10 | 📚 建议重新开始 | 从 [Type System](04_type_system.md) 逐节阅读，配合 [crates/c02_type_system](../../crates/c02_type_system) 示例 |

---

> **对应 Crate**: [`c02_type_system`](../../crates/c02_type_system)
> **对应练习**: [`exercises/src/type_system/`](../../exercises/src/type_system)

---

> **权威来源**: [The Rust Programming Language — Ch3](https://doc.rust-lang.org/book/ch03-00-common-programming-concepts.html) · [The Rust Programming Language — Ch6](https://doc.rust-lang.org/book/ch06-00-enums.html) · [Rust Reference — Types](https://doc.rust-lang.org/reference/types.html)

## 嵌入式测验（Embedded Quiz）

### 测验 1：本文件是 测验：类型系统（试点扩展） 的专项测验集。这类测验文件的主要作用是什么？（理解层）

**题目**: 本文件是 测验：类型系统（Type System）（试点扩展） 的专项测验集。这类测验文件的主要作用是什么？

<details>
<summary>✅ 答案与解析</summary>

集中提供大量针对特定主题的练习题，帮助学习者系统检验和巩固对该主题的掌握程度，补充概念文件中的嵌入式测验。
</details>

---

### 测验 2：在 测验：类型系统（试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？（理解层）

**题目**: 在 测验：类型系统（Type System）（试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？

<details>
<summary>✅ 答案与解析</summary>

先尝试独立作答，然后对照答案解析理解错误原因，最后回到对应的概念文件重新阅读相关章节，形成"测验-反馈-复习"的闭环。
</details>

---

### 测验 3：专项测验与概念文件末尾的嵌入式测验有什么区别？（理解层）

**题目**: 专项测验与概念文件末尾的嵌入式测验有什么区别？

<details>
<summary>✅ 答案与解析</summary>

专项测验题量更大、覆盖更全面，通常按难度分层；嵌入式测验更精简，直接关联刚阅读的概念内容，用于即时检验理解。
</details>
