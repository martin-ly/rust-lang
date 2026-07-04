> **内容分级**: [专家级]

# 测验：宏系统（L3 试点扩展）
>
> **EN**: Macros
> **Summary**: Quiz Macros. Core Rust concept.
> **答案**： ```rust // vec![1, 2, 3] 展开为： { let mut temp_vec = Vec::new(); temp_vec.push(1); temp_vec.push(2); temp_vec.push(3); temp_vec }```
> **解析**：`vec!` 是 Rust 标准库中的**声明宏**（declarative macro），使用 `macro_rules!` 定义。
> **声明宏（Declarative Macro）的核心特征**： | 特性 | 说明 | |:---|:---| | 调用语法
> **受众**: [专家]
> **内容分级**: [专家级]
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链
> **后置概念**: N/A
---

> **来源**: · [宏系统](04_macros.md) · [Kohlbecker et al. — Hygienic Macro Expansion](https://doi.org/10.1145/41625.41632) · [Flatt — Binding as Sets of Scopes](https://doi.org/10.1145/2814304.2814305) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Oxide: The Essence of Rust](https://arxiv.org/abs/1903.00982) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [The Rust Programming Language — Ch19.5 Macros](https://doc.rust-lang.org/book/ch19-06-macros.html) ·
> [The Little Book of Rust Macros](https://danielkeep.github.io/tlborm/book/) ·
> [Rust Reference — Macros](https://doc.rust-lang.org/reference/macros.html)
>
> **前置概念**: [宏（Macro）模式](../02_intermediate/17_macro_patterns.md)
> [Macros](04_macros.md) ·
> [Proc Macros](07_proc_macro.md) ·
> [Type System](../01_foundation/04_type_system.md)
>
> **对应练习**:
> [`exercises/src/macros/`](../../exercises/src/macros)

---

> **Bloom 层级**: 应用 → 分析
> **定位**: L3 嵌入式互动测验——验证宏系统核心概念（声明宏（Declarative Macro） `macro_rules!`、重复模式、卫生性、过程宏（Procedural Macro））的掌握程度。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---


---

## 认知路径

> **认知路径**: 本节从 "测验" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 测验 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 测验 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与测验的适用边界。
5. **迁移应用**: 将 测验 与前置/后置概念链接，形成跨层知识网络。


---

> **过渡**: 从 测验 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 测验 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 测验 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。


---

> **定理 1** [Tier 2]: 测验 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 测验 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 测验 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。


---

## 反命题决策树

> **反命题 1**: "测验 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 测验 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 测验 规则被违反的直接信号。

> **反命题 3**: "其他语言对 测验 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 测验 具有语言特有的形态。


---

> **反向推理 1**: 如果程序在 测验 相关代码处出现编译错误 ⟸ 应首先检查所有权（Ownership）、生命周期（Lifetimes）或类型约束是否被违反。
>
> **反向推理 2**: 如果某段代码在运行时（Runtime）表现出非预期行为且与 测验 有关 ⟸ 应回溯到其形式化语义或安全边界假设，定位隐式契约。


## 一、声明宏基础

### Q1. 以下宏调用 `vec![1, 2, 3]` 展开后近似于什么代码？

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

```rust,compile_fail
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

**声明宏（Macro）的核心特征**：

| 特性 | 说明 |
|:---|:---|
| 调用语法 | `name![...]` / `name!(...)` / `name!{...}` |
| 展开时机 | 编译期（词法分析后，AST 构造前） |
| 卫生性 | 半卫生（semi-hygienic）：局部变量不冲突，但路径可能冲突 |
| 递归 | 支持递归调用自身 |

**对比**：

| 宏（Macro）类型 | 展开阶段 | 输入 | 输出 |
|:---|:---|:---|:---|
| 声明宏（Declarative Macro） `macro_rules!` | 早期（token 树） | token 树 | token 树 |
| 过程宏（Procedural Macro） `derive` | 后期（AST） | AST | AST |
| 过程宏（Procedural Macro） `proc_macro` | 后期（token 流） | token 流 | token 流 |

**知识点**：声明宏（Declarative Macro）是 Rust 中最早的宏形式，适合简单的代码生成和 DSL。复杂场景（如 derive）应使用过程宏（Procedural Macro）。→ 宏系统详解

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

```text
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

```rust,compile_fail
{
    let mut temp = 0;
    temp += 1;
    temp += 2;
    temp += 3;
    temp
}
```

**注意**：`sum!()` 匹配零次，展开为 `temp = 0`，返回 0。

**知识点**：重复模式是声明宏（Declarative Macro）最强大的特性，允许处理任意数量的参数。分隔符的选择影响宏的调用语法。[→ 宏系统详解](04_macros.md)

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

**解析**：Rust 的声明宏（Macro）是**半卫生（semi-hygienic）**的。

**卫生性含义**：宏（Macro）内部定义的变量不会与外部变量冲突，但**从外部传入的标识符**仍引用（Reference）外部作用域。

**执行分析**：

```rust
// using_a!(println!("{}", a)) 展开为：
{
    let a = 42;           // 宏内部定义的 a，与外部隔离
    println!("{}", a);    // ❌ 等一下——这里的 a 是哪个？
}
```

实际上输出是 `outer`。这是因为 Rust 的卫生性规则：**宏（Macro）参数中使用的标识符在宏定义处解析**。

但等一下，这个例子实际上是复杂的。让我澄清：

在 Rust 中，`$e:expr` 参数中的 `a` 是在**调用点**解析的，因此它引用（Reference） `main` 中的 `a = "outer"`。宏内部 `let a = 42` 是宏自己生成的变量，与参数中的 `a` 隔离。

**对比 C 预处理器**：

```c
#define SWAP(a, b) { int temp = a; a = b; b = temp; }
// C 中：SWAP(x, temp) 会导致变量名冲突！
```

Rust 的卫生性避免了这种经典宏陷阱。

**知识点**：卫生性是 Rust 宏相对于 C 预处理器的关键优势，但理解"哪些标识符在何处解析"对调试宏仍然重要。[→ 宏系统详解](04_macros.md)

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

**解析**：`#[derive(...)]` 是**派生宏（derive macro）**，编译器自动为结构体（Struct）生成 trait 实现。

**生成的代码近似于**：

```rust,ignore
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

**自定义 derive**：通过 `proc_macro_derive` 创建自己的 derive 宏（Macro）。

**知识点**：derive 宏是最常用的过程宏（Procedural Macro），消除了大量 boilerplate。理解其生成的代码有助于调试复杂的 trait 约束问题。[→ 过程宏详解](07_proc_macro.md)

</details>

---

### Q5. 以下代码能否编译？解释属性宏（Attribute Macro）与函数宏的区别

```rust,ignore
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

**三种过程宏（Procedural Macro）**：

| 类型 | 定义方式 | 用途 | 示例 |
|:---|:---|:---|:---|
| 派生宏 | `#[proc_macro_derive(Name)]` | 为类型自动实现 trait | `#[derive(Debug)]` |
| 属性宏 | `#[proc_macro_attribute]` | 修改/包装函数/结构体（Struct） | `#[trace]`、`#[test]` |
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

- 属性宏：**修改**已有 AST 节点（函数、结构体（Struct）等）
- 函数宏（`proc_macro`）：**生成**新代码，通过 `!` 调用

**知识点**：属性宏是构建编译期 AOP（面向切面编程）和代码生成工具的核心机制。`tokio::main`、`test`、`derive` 都是属性宏。[→ 过程宏（Procedural Macro）详解](07_proc_macro.md)

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
| `lifetime` | 生命周期（Lifetimes） | `'a`、`'static` |
| `meta` | 属性内容 | `derive(Debug)`、`cfg(test)` |
| `vis` | 可见性 | `pub`、`pub(crate)` |

**选择建议**：

- 需要表达式语义 → 用 `expr`
- 需要最大灵活性 → 用 `tt`（但可能匹配不期望的内容）
- 需要类型检查 → 用 `ty`

**知识点**：fragment specifier 的选择直接影响宏的健壮性和错误信息质量。过于宽泛的 `tt` 会导致难以调试的展开错误。[→ 宏系统详解](04_macros.md)

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

```rust,ignore
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

**知识点**：递归宏是实现编译期计算（如类型列表长度、位掩码生成）的强大工具，但受限于编译器的递归深度。[→ 宏系统详解](04_macros.md)

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

| 宏（Macro） | 输入 | 输出 | 返回类型 |
|:---|:---|:---|:---|
| `stringify!($tokens)` | 任意 token | token 的字符串表示 | `&'static str` |
| `concat!("a", "b", ...)` | 字符串字面量 + 整数/布尔常量 | 拼接后的字符串 | `&'static str` |
| `line!()` | 无 | 当前行号 | `u32` |
| `file!()` | 无 | 当前文件名 | `&'static str` |
| `module_path!()` | 无 | 当前模块（Module）路径 | `&'static str` |
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

**知识点**：内置宏（built-in macros）是 Rust 编译器提供的特殊宏，在标准库中声明但实际由编译器直接处理。[→ 宏系统详解](04_macros.md)

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

```rust,compile_fail
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

**知识点**：分隔符在宏定义和展开中必须一致。常见的错误是匹配时用了逗号分隔，但展开时忘了添加分隔符。[→ 宏系统详解](04_macros.md)

</details>

---

### Q10. 以下代码存在什么问题？这是宏与模块交互的经典陷阱

```rust,compile_fail
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

**解析**：`use_std!()` 展开为 `use std::vec::Vec;`，但这在 `inner` 模块（Module）中引入的是 `inner::Vec`，而调用时写的是 `Vec::new()`（相对路径）。

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

1. 宏中引用（Reference）的外部类型应使用**绝对路径**（`::std::...`）
2. 如果宏在库 crate 中定义并引用（Reference）自己的类型，使用 `$crate`
3. 避免在宏中生成 `use` 语句，直接写全路径

**知识点**：宏的展开位置影响路径解析。这是宏从"原型"走向"生产级"时必须处理的问题。[→ 宏系统详解](04_macros.md)

</details>

---

## 五、评分参考

| 得分 | 评价 | 建议 |
|:---:|:---|:---|
| 10/10 | 🏆 宏系统已内化 | 尝试为 crates/ 编写自定义 derive 或属性宏 |
| 7–9/10 | ✅ 核心概念掌握 | 强化 [宏练习](../../exercises/src/macros)，阅读 `vec!` 等标准宏的源码 |
| 4–6/10 | 🔄 需巩固基础 | 重读 [Macros](04_macros.md) · [Proc Macros](07_proc_macro.md) |
| 0–3/10 | 📚 建议重新开始 | 从 [宏基础](../01_foundation/12_attributes_and_macros.md) 开始，配合 [TLBoRM](https://danielkeep.github.io/tlborm/book/) |

---

> **对应 Crate**: [`c11_macro_system_proc`](../../crates/c11_macro_system_proc)
> **对应练习**: [`exercises/src/macros/`](../../exercises/src/macros)

---

> **权威来源**: [The Rust Programming Language — Ch19.5](https://doc.rust-lang.org/book/ch19-06-macros.html) · [The Little Book of Rust Macros](https://danielkeep.github.io/tlborm/book/) · [Rust Reference — Macros](https://doc.rust-lang.org/reference/macros.html)

## 嵌入式测验（Embedded Quiz）

### 测验 1：本文件是 测验：宏系统（L3 试点扩展） 的专项测验集。这类测验文件的主要作用是什么？（理解层）

**题目**: 本文件是 测验：宏系统（L3 试点扩展） 的专项测验集。这类测验文件的主要作用是什么？

<details>
<summary>✅ 答案与解析</summary>

集中提供大量针对特定主题的练习题，帮助学习者系统检验和巩固对该主题的掌握程度，补充概念文件中的嵌入式测验。
</details>

---

### 测验 2：在 测验：宏系统（L3 试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？（理解层）

**题目**: 在 测验：宏系统（L3 试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？

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
