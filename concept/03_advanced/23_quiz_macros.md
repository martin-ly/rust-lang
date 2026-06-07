> **内容分级**: [专家级]

# 测验：宏系统（L3 试点扩展）
> **EN**: Macros
> **Summary**: <details> <summary>💡 点击展开答案与解析</summary> **答案**： ```rust // vec![1, 2, 3] 展开为： { let mut temp_vec = Vec::new(); temp_vec.push(1); temp_vec.push(2); temp_vec.push(3); temp_vec } ``` **解析**：`vec!` 是 Rust 标准库中的**声明宏**（declarative macro），使用 `macro_rules!` 定义。 **声明宏的核心特征**： | 特性 | 说明 | |:---|:---| | 调用语法

> **受众**: [专家]
> **内容分级**: [专家级]
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链

---

> **来源**:
> [The Rust Programming Language — Ch19.5 Macros](https://doc.rust-lang.org/book/ch19-06-macros.html) ·
> [The Little Book of Rust Macros](https://danielkeep.github.io/tlborm/book/) ·
> [Rust Reference — Macros](https://doc.rust-lang.org/reference/macros.html)
>
> **前置概念**:
> [Macros](./04_macros.md) ·
> [Proc Macros](./07_proc_macro.md) ·
> [Type System](../01_foundation/04_type_system.md)
>
> **对应练习**:
> [`exercises/src/macros/`](../../exercises/src/macros/)

---

> **Bloom 层级**: 应用 → 分析
> **定位**: L3 嵌入式互动测验——验证宏系统核心概念（声明宏 `macro_rules!`、重复模式、卫生性、过程宏）的掌握程度。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

## 一、声明宏基础

### Q1. 以下宏调用 `vec![1, 2, 3]` 展开后近似于什么代码？

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

```rust
// vec![1, 2, 3] 展开为：
{
    let mut temp_vec = Vec::new();
    temp_vec.push(1);
    temp_vec.push(2);
    temp_vec.push(3);
    temp_vec
}
```

**解析**：`vec!` 是 Rust 标准库中的**声明宏**（declarative macro），使用 `macro_rules!` 定义。

**声明宏的核心特征**：

| 特性 | 说明 |
|:---|:---|
| 调用语法 | `name![...]` / `name!(...)` / `name!{...}` |
| 展开时机 | 编译期（词法分析后，AST 构造前） |
| 卫生性 | 半卫生（semi-hygienic）：局部变量不冲突，但路径可能冲突 |
| 递归 | 支持递归调用自身 |

**对比**：

| 宏类型 | 展开阶段 | 输入 | 输出 |
|:---|:---|:---|:---|
| 声明宏 `macro_rules!` | 早期（token 树） | token 树 | token 树 |
| 过程宏 `derive` | 后期（AST） | AST | AST |
| 过程宏 `proc_macro` | 后期（token 流） | token 流 | token 流 |

**知识点**：声明宏是 Rust 中最早的宏形式，适合简单的代码生成和 DSL。复杂场景（如 derive）应使用过程宏。[→ 宏系统详解](./04_macros.md)

</details>

---

### Q2. 以下代码能否编译？解释宏的重复模式

```rust
macro_rules! sum {
    ($($x:expr),*) => {
        {
            let mut temp = 0;
            $(
                temp += $x;
            )*
            temp
        }
    };
}

fn main() {
    println!("{}", sum!(1, 2, 3));
    println!("{}", sum!());
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出：

```
6
0
```

**解析**：`$($x:expr),*` 是**重复模式**（repetition pattern）。

| 重复运算符 | 含义 | 最少匹配 |
|:---|:---|:---:|
| `*` | 零次或多次 | 0 |
| `+` | 一次或多次 | 1 |
| `?` | 零次或一次 | 0 |

**分隔符**：

```rust
// $(...),*  → 逗号分隔
// $(...);*  → 分号分隔
// $(...)*   → 无分隔符
```

**展开过程**（`sum!(1, 2, 3)`）：

```rust
{
    let mut temp = 0;
    temp += 1;
    temp += 2;
    temp += 3;
    temp
}
```

**注意**：`sum!()` 匹配零次，展开为 `temp = 0`，返回 0。

**知识点**：重复模式是声明宏最强大的特性，允许处理任意数量的参数。分隔符的选择影响宏的调用语法。[→ 宏系统详解](./04_macros.md)

</details>

---

### Q3. 以下代码能否编译？解释宏的**卫生性（Hygiene）**

```rust
macro_rules! using_a {
    ($e:expr) => {
        {
            let a = 42;
            $e
        }
    };
}

fn main() {
    let a = "outer";
    let x = using_a!(println!("{}", a));
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出 `outer`。

**解析**：Rust 的声明宏是**半卫生（semi-hygienic）**的。

**卫生性含义**：宏内部定义的变量不会与外部变量冲突，但**从外部传入的标识符**仍引用外部作用域。

**执行分析**：

```rust
// using_a!(println!("{}", a)) 展开为：
{
    let a = 42;           // 宏内部定义的 a，与外部隔离
    println!("{}", a);    // ❌ 等一下——这里的 a 是哪个？
}
```

实际上输出是 `outer`。这是因为 Rust 的卫生性规则：**宏参数中使用的标识符在宏定义处解析**。

但等一下，这个例子实际上是复杂的。让我澄清：

在 Rust 中，`$e:expr` 参数中的 `a` 是在**调用点**解析的，因此它引用 `main` 中的 `a = "outer"`。宏内部 `let a = 42` 是宏自己生成的变量，与参数中的 `a` 隔离。

**对比 C 预处理器**：

```c
#define SWAP(a, b) { int temp = a; a = b; b = temp; }
// C 中：SWAP(x, temp) 会导致变量名冲突！
```

Rust 的卫生性避免了这种经典宏陷阱。

**知识点**：卫生性是 Rust 宏相对于 C 预处理器的关键优势，但理解"哪些标识符在何处解析"对调试宏仍然重要。[→ 宏系统详解](./04_macros.md)

</details>

---

## 二、过程宏

### Q4. 以下代码的输出是什么？解释 `derive` 宏的工作原理

```rust
#[derive(Debug, Clone, PartialEq)]
struct Point {
    x: i32,
    y: i32,
}

fn main() {
    let p1 = Point { x: 1, y: 2 };
    let p2 = p1.clone();
    println!("{:?}", p1 == p2);
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：`true`

**解析**：`#[derive(...)]` 是**派生宏（derive macro）**，编译器自动为结构体生成 trait 实现。

**生成的代码近似于**：

```rust
impl Debug for Point { /* 自动实现 */ }
impl Clone for Point {
    fn clone(&self) -> Self {
        Point {
            x: self.x.clone(),
            y: self.y.clone(),
        }
    }
}
impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}
```

**derive 的限制**：

| 限制 | 说明 |
|:---|:---|
| 只能为 struct/enum 实现 | 不能为 trait/函数/type alias |
| 字段类型必须已实现对应 trait | `Point<T>` 需要 `T: Debug + Clone + PartialEq` |
| 不能自定义逻辑 | 只能生成"标准"实现 |

**自定义 derive**：通过 `proc_macro_derive` 创建自己的 derive 宏。

**知识点**：derive 宏是最常用的过程宏，消除了大量 boilerplate。理解其生成的代码有助于调试复杂的 trait 约束问题。[→ 过程宏详解](./07_proc_macro.md)

</details>

---

### Q5. 以下代码能否编译？解释属性宏（Attribute Macro）与函数宏的区别

```rust
// 假设有一个 `trace` 属性宏
#[trace]
fn add(a: i32, b: i32) -> i32 {
    a + b
}

fn main() {
    println!("{}", add(1, 2));
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：假设 `trace` 宏已正确定义，✅ 能编译。

**解析**：属性宏（Attribute Macro）可以**修改**（甚至替换）被标注的项。

**三种过程宏**：

| 类型 | 定义方式 | 用途 | 示例 |
|:---|:---|:---|:---|
| 派生宏 | `#[proc_macro_derive(Name)]` | 为类型自动实现 trait | `#[derive(Debug)]` |
| 属性宏 | `#[proc_macro_attribute]` | 修改/包装函数/结构体 | `#[trace]`、`#[test]` |
| 函数式宏 | `#[proc_macro]` | 像函数一样调用，操作 token | `sql!(SELECT * FROM users)` |

**`#[trace]` 可能的展开**：

```rust
fn add(a: i32, b: i32) -> i32 {
    println!("Entering add(a={a}, b={b})");
    let result = {
        a + b
    };
    println!("Exiting add with result={result}");
    result
}
```

**属性宏 vs 函数宏**：

- 属性宏：**修改**已有 AST 节点（函数、结构体等）
- 函数宏（`proc_macro`）：**生成**新代码，通过 `!` 调用

**知识点**：属性宏是构建编译期 AOP（面向切面编程）和代码生成工具的核心机制。`tokio::main`、`test`、`derive` 都是属性宏。[→ 过程宏详解](./07_proc_macro.md)

</details>

---

## 三、宏的高级技巧

### Q6. 以下代码能否编译？`tt` 和 `expr` 的区别是什么？

```rust
macro_rules! print_expr {
    ($e:expr) => {
        println!("Expression: {}", stringify!($e));
        println!("Value: {}", $e);
    };
}

fn main() {
    print_expr!(1 + 2);
    print_expr!({ let x = 5; x * 2 });
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出：

```
Expression: 1 + 2
Value: 3
Expression: { let x = 5 ; x * 2 }
Value: 10
```

**解析**：`$e:expr` 匹配**完整表达式**，而 `$e:tt`（token tree）匹配任意单个 token 树。

**Fragment Specifier 速查**：

| Specifier | 匹配内容 | 示例 |
|:---|:---|:---|
| `expr` | 完整表达式 | `1 + 2`、`foo()`、`{ block }` |
| `ty` | 类型 | `i32`、`Vec<T>`、`impl Trait` |
| `pat` | 模式 | `x`、`Some(x)`、`_` |
| `stmt` | 语句 | `let x = 5;`、`foo()` |
| `block` | 代码块 | `{ let x = 5; x }` |
| `item` | 项 | `fn`、`struct`、`use` |
| `path` | 路径 | `std::vec::Vec`、`foo::bar` |
| `tt` | 任意 token 树 | 最灵活，但限制最少 |
| `literal` | 字面量 | `"hello"`、`42`、`3.14` |
| `ident` | 标识符 | `foo`、`_bar` |
| `lifetime` | 生命周期 | `'a`、`'static` |
| `meta` | 属性内容 | `derive(Debug)`、`cfg(test)` |
| `vis` | 可见性 | `pub`、`pub(crate)` |

**选择建议**：

- 需要表达式语义 → 用 `expr`
- 需要最大灵活性 → 用 `tt`（但可能匹配不期望的内容）
- 需要类型检查 → 用 `ty`

**知识点**：fragment specifier 的选择直接影响宏的健壮性和错误信息质量。过于宽泛的 `tt` 会导致难以调试的展开错误。[→ 宏系统详解](./04_macros.md)

</details>

---

### Q7. 以下代码能否编译？宏递归的限制是什么？

```rust
macro_rules! count {
    () => { 0 };
    ($x:tt $($rest:tt)*) => { 1 + count!($($rest)*) };
}

fn main() {
    println!("{}", count!(a b c d e));
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出 `5`。

**解析**：递归宏通过**基础情形**（`() => { 0 }`）和**递归情形**（`$x:tt $($rest:tt)*`）实现。

**展开过程**（`count!(a b c d e)`）：

```rust
count!(a b c d e)
→ 1 + count!(b c d e)
→ 1 + 1 + count!(c d e)
→ 1 + 1 + 1 + count!(d e)
→ 1 + 1 + 1 + 1 + count!(e)
→ 1 + 1 + 1 + 1 + 1 + count!()
→ 1 + 1 + 1 + 1 + 1 + 0
→ 5
```

**递归限制**：

Rust 编译器对宏递归深度有上限（默认 128）。超过会报错：

```
recursion limit reached while expanding macro
```

可通过属性增加限制：

```rust
#![recursion_limit = "256"]
```

**尾递归优化**：宏展开没有尾递归优化，每次递归都会增加展开深度。

**知识点**：递归宏是实现编译期计算（如类型列表长度、位掩码生成）的强大工具，但受限于编译器的递归深度。[→ 宏系统详解](./04_macros.md)

</details>

---

## 四、综合应用

### Q8. 以下代码的输出是什么？`concat!` 和 `stringify!` 的区别

```rust
fn main() {
    println!("{}", stringify!(1 + 2));
    println!("{}", concat!("Hello", " ", "World"));
    println!("{}", concat!("Line: ", line!()));
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

```
1 + 2
Hello World
Line: 8
```

**解析**：

| 宏 | 输入 | 输出 | 返回类型 |
|:---|:---|:---|:---|
| `stringify!($tokens)` | 任意 token | token 的字符串表示 | `&'static str` |
| `concat!("a", "b", ...)` | 字符串字面量 + 整数/布尔常量 | 拼接后的字符串 | `&'static str` |
| `line!()` | 无 | 当前行号 | `u32` |
| `file!()` | 无 | 当前文件名 | `&'static str` |
| `module_path!()` | 无 | 当前模块路径 | `&'static str` |
| `column!()` | 无 | 当前列号 | `u32` |

**使用场景**：

```rust
// 编译期构建标识符
macro_rules! make_fn {
    ($name:ident) => {
        fn $name() { println!("Called {}", stringify!($name)); }
    };
}

make_fn!(foo); // 生成 fn foo() { ... }
```

**知识点**：内置宏（built-in macros）是 Rust 编译器提供的特殊宏，在标准库中声明但实际由编译器直接处理。[→ 宏系统详解](./04_macros.md)

</details>

---

### Q9. 以下代码能否编译？宏中的 `$(...)*` 与 `$(...),*` 的区别

```rust
macro_rules! build_array {
    ($($x:expr),*) => {
        [$($x),*]
    };
}

fn main() {
    let arr = build_array!(1, 2, 3);
    println!("{:?}", arr);
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，`arr` 类型为 `[i32; 3]`，输出 `[1, 2, 3]`。

**解析**：

```rust
// build_array!(1, 2, 3) 展开为：
[1, 2, 3]
```

**分隔符匹配的陷阱**：

```rust
macro_rules! bad {
    ($($x:expr),*) => { $( $x )* }; // ❌ 错误：无分隔符
}

// bad!(1, 2, 3) 展开为：
// 1 2 3  // 语法错误！
```

**正确做法**：

```rust
macro_rules! good {
    ($($x:expr),*) => { [$( $x ),*] }; // ✅ 逗号分隔
    ($($x:expr);*) => { [$( $x ),*] }; // ✅ 也支持分号分隔的调用
}
```

**注意**：`$(...),*` 在匹配时允许**末尾逗号**（trailing comma），但展开时不会生成末尾逗号。

**知识点**：分隔符在宏定义和展开中必须一致。常见的错误是匹配时用了逗号分隔，但展开时忘了添加分隔符。[→ 宏系统详解](./04_macros.md)

</details>

---

### Q10. 以下代码存在什么问题？这是宏与模块交互的经典陷阱

```rust
macro_rules! use_std {
    () => {
        use std::vec::Vec;
    };
}

mod inner {
    use_std!();

    fn foo() {
        let _v = Vec::new();
    }
}

fn main() {}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`Vec` is not found in this scope`

**解析**：`use_std!()` 展开为 `use std::vec::Vec;`，但这在 `inner` 模块中引入的是 `inner::Vec`，而调用时写的是 `Vec::new()`（相对路径）。

**修正方案**——在宏中使用绝对路径：

```rust
macro_rules! use_std {
    () => {
        use ::std::vec::Vec; // 注意开头的 ::
    };
}
```

或使用 `$crate`（更 robust）：

```rust
macro_rules! make_vec {
    ($($x:expr),*) => {
        $crate::std::vec::Vec::from([$($x),*])
    };
}
```

**`$crate` 的作用**：指向定义宏的 crate，避免路径解析歧义。

**最佳实践**：

1. 宏中引用的外部类型应使用**绝对路径**（`::std::...`）
2. 如果宏在库 crate 中定义并引用自己的类型，使用 `$crate`
3. 避免在宏中生成 `use` 语句，直接写全路径

**知识点**：宏的展开位置影响路径解析。这是宏从"原型"走向"生产级"时必须处理的问题。[→ 宏系统详解](./04_macros.md)

</details>

---

## 五、评分参考

| 得分 | 评价 | 建议 |
|:---:|:---|:---|
| 10/10 | 🏆 宏系统已内化 | 尝试为 crates/ 编写自定义 derive 或属性宏 |
| 7–9/10 | ✅ 核心概念掌握 | 强化 [宏练习](../../exercises/src/macros/)，阅读 `vec!` 等标准宏的源码 |
| 4–6/10 | 🔄 需巩固基础 | 重读 [Macros](./04_macros.md) · [Proc Macros](./07_proc_macro.md) |
| 0–3/10 | 📚 建议重新开始 | 从 [宏基础](../01_foundation/12_attributes_and_macros.md) 开始，配合 [TLBoRM](https://danielkeep.github.io/tlborm/book/) |

---

> **对应 Crate**: [`c11_macro_system`](../../crates/c11_macro_system/) · [`c11_macro_system_proc`](../../crates/c11_macro_system_proc/)
> **对应练习**: [`exercises/src/macros/`](../../exercises/src/macros/)

---

> **权威来源**: [The Rust Programming Language — Ch19.5](https://doc.rust-lang.org/book/ch19-06-macros.html) · [The Little Book of Rust Macros](https://danielkeep.github.io/tlborm/book/) · [Rust Reference — Macros](https://doc.rust-lang.org/reference/macros.html)
