> **内容分级**: [综述级]
>
# Rust 关键字（Keywords）

> **EN**: Keywords
> **Summary**: Rust 中保留给当前或未来语言使用的关键字列表，以及 raw identifier（原始标识符）用法。
>
> **受众**: [初学者]
> **Bloom 层级**: 记忆 → 理解
> **A/S/P 标记**: **S** — Specification / Language syntax
> **双维定位**: S×Lang — 语言词法与语法
> **前置依赖**: [Identifiers and Names](20_variable_model.md) · [Terminology Glossary](../00_meta/terminology_glossary.md)
> **后置概念**: [Attributes and Macros](12_attributes_and_macros.md) · [Modules and Paths](11_modules_and_paths.md)
> **定理链**: N/A — 参考级文档
>
> **来源**: [TRPL — Appendix A: Keywords](https://doc.rust-lang.org/book/appendix-01-keywords.html) · [Rust Reference — Keywords](https://doc.rust-lang.org/reference/keywords.html)

---

## 一、关键字概述

关键字（keywords）是 Rust 保留给语言本身使用的词，**不能用作标识符**（变量名、函数名、类型名等），除非使用 **raw identifier** 语法 `r#`。

标识符包括：函数、变量、参数、struct 字段、模块、crate、常量、宏、静态值、属性、类型、trait、生命周期的名字。

---

## 二、当前使用的关键字

| 关键字 | 作用 |
|:---|:---|
| `as` | 原始类型转换、trait 消歧、`use` 重命名 |
| `async` | 返回 `Future` 而非阻塞当前线程 |
| `await` | 挂起执行直到 `Future` 就绪 |
| `break` | 立即退出循环 |
| `const` | 定义常量或常量原始指针 |
| `continue` | 跳到下一次循环迭代 |
| `crate` | 模块路径中指代 crate root |
| `dyn` | trait object 动态分发 |
| `else` | `if` / `if let` 的 fallback 分支 |
| `enum` | 定义枚举 |
| `extern` | 链接外部函数或变量 |
| `false` | 布尔假字面量 |
| `fn` | 定义函数或函数指针类型 |
| `for` | 迭代循环、trait 实现、高阶生命周期 |
| `if` | 条件分支 |
| `impl` | 实现 inherent 或 trait 功能 |
| `in` | `for` 循环语法的一部分 |
| `let` | 绑定变量 |
| `loop` | 无条件循环 |
| `match` | 模式匹配 |
| `mod` | 定义模块 |
| `move` | 使闭包获取所有捕获变量的所有权 |
| `mut` | 标注引用、原始指针或模式绑定的可变性 |
| `pub` | 标注 struct 字段、`impl` 块或模块的公开可见性 |
| `ref` | 按引用绑定 |
| `return` | 从函数返回 |
| `Self` | 正在定义或实现的类型的别名 |
| `self` | 方法接收者或当前模块 |
| `static` | 全局变量或贯穿整个程序执行的生命周期 |
| `struct` | 定义结构体 |
| `super` | 当前模块的父模块 |
| `trait` | 定义 trait |
| `true` | 布尔真字面量 |
| `type` | 定义类型别名或关联类型 |
| `union` | 定义 union（仅在 union 声明中是关键字） |
| `unsafe` | 标注 unsafe 代码、函数、trait 或实现 |
| `use` | 将符号引入作用域 |
| `where` | 标注类型约束从句 |
| `while` | 条件循环 |

---

## 三、保留给未来使用的关键字

以下关键字目前没有功能，但被 Rust 保留以备将来使用：

| 关键字 | 备注 |
|:---|:---|
| `abstract` | 潜在用于抽象类型 |
| `become` | 潜在用于尾调用/转换语义 |
| `box` | 与堆分配相关的历史保留 |
| `do` | 潜在用于 do-notation |
| `final` | 潜在用于不可覆写 |
| `gen` | 潜在用于生成器语法 |
| `macro` | 潜在用于宏相关保留 |
| `override` | 潜在用于覆写标记 |
| `priv` | 潜在用于私有性 |
| `try` | 2018+ 版本中为保留关键字 |
| `typeof` | 潜在用于类型查询 |
| `unsized` | 潜在用于 unsized 类型标记 |
| `virtual` | 潜在用于虚方法 |
| `yield` | 潜在用于生成器 yield |

---

## 四、Raw Identifiers（原始标识符）

使用 `r#` 前缀可以将关键字当作普通标识符使用。

```rust
fn r#match(needle: &str, haystack: &str) -> bool {
    haystack.contains(needle)
}

fn main() {
    assert!(r#match("foo", "foobar"));
}
```

### 典型使用场景

1. **与使用关键字作为名称的代码集成**：例如旧版库使用了 `try` 作为函数名。
2. **跨 Edition 调用**：`try` 在 2015 Edition 不是关键字，但在 2018/2021/2024 中是保留关键字。调用 2015 Edition 库中的 `try` 函数时需要 `r#try`。

> **注意**：raw identifier 只影响词法层面，类型/函数名在编译后不再带有 `r#`。

---

## 五、实践建议

1. **避免使用关键字作为标识符**，即使 raw identifier 允许。
2. **跨 edition 依赖时留意保留关键字变化**：2015 → 2018 的 `try`、`async`、`await` 等。
3. **宏生成代码中可能需要 raw identifier**：当宏接收用户输入并需要生成以关键字命名的字段/变量时。

---

## 六、关联概念

| 概念 | 关系 |
|:---|:---|
| [Modules and Paths](11_modules_and_paths.md) | `crate`、`self`、`super` 用于路径 |
| [Attributes and Macros](12_attributes_and_macros.md) | 宏可能生成以关键字命名的标识符 |
| [Control Flow](07_control_flow.md) | `if`、`else`、`match`、`loop`、`while`、`for`、`break`、`continue` 控制流关键字 |
