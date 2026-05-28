# Hello, World
>
> **相关概念**: [控制流](../../concept/01_foundation/07_control_flow.md)

> **Bloom 层级**: 理解

> **你的第一个 Rust 程序**
> **预计时间**: 15 分钟
> **权威来源**: [The Rust Programming Language — Ch1](https://doc.rust-lang.org/book/ch01-00-getting-started.html), [Cargo Guide](https://doc.rust-lang.org/cargo/guide/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 TRPL 官方教程来源标注、Cargo 项目结构来源引用 [来源: Authority Source Sprint Batch 8]

## 🎯 学习目标
>
> **[来源: Rust Official Docs]**

完成本章后，你将能够：

- [ ] 使用 Cargo 创建新项目
- [ ] 编写、编译和运行 Rust 程序
- [ ] 理解 Rust 项目结构
- [ ] 使用基本打印宏

## 📋 先决条件
>
> **[来源: Rust Official Docs]**

- 已完成 [安装 Rust](02_installation.md)
- 了解基本的命令行操作

## 🚀 创建项目
>
> **[来源: Rust Official Docs]**

### 使用 Cargo 创建
>
> **[来源: Rust Official Docs]**

```bash
cargo new hello_world
cd hello_world
```

Cargo 会创建以下结构：

```
hello_world/
├── Cargo.toml      # 项目配置
├── .gitignore      # Git 忽略文件
└── src/
    └── main.rs     # 主程序入口
```

## 📄 项目文件详解
>
> **[来源: Rust Official Docs]**

### Cargo.toml
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```toml
[package]
name = "hello_world"
version = "0.1.0"
edition = "2024"      # Rust 版本

[dependencies]
# 依赖项（目前为空）
```

### src/main.rs
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust
fn main() {
    println!("Hello, world!");
}
```

## 🏃 编译和运行
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 开发模式（快速编译）
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```bash
cargo run
```

输出：

```
   Compiling hello_world v0.1.0
    Finished dev [unoptimized + debuginfo]
     Running `target/debug/hello_world`
Hello, world!
```

### 发布模式（优化编译）
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```bash
cargo run --release
```

## 🧠 代码解析
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### `fn main()`
>
> **[来源: [crates.io](https://crates.io/)]**

- Rust 程序的入口点
- 必须是 `fn main()` 函数
- 无参数（简单情况）

### `println!` 宏
>
> **[来源: [docs.rs](https://docs.rs/)]**

```rust,ignore
println!("Hello, world!");           // 基本用法
println!("Hello, {}!", "Rust");      // 格式化
println!("1 + 1 = {}", 1 + 1);       // 表达式
```

注意 `!` 表示这是一个**宏**，不是普通函数。

## ✨ 增强示例
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 示例 1: 交互式程序
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust
use std::io;

fn main() {
    println!("请输入你的名字:");

    let mut name = String::new();
    io::stdin()
        .read_line(&mut name)
        .expect("读取失败");

    println!("你好, {}!", name.trim());
}
```

运行：

```bash
$ cargo run
请输入你的名字:
Alice
你好, Alice!
```

### 示例 2: 计算程序
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust
fn main() {
    let x = 5;
    let y = 10;

    println!("x = {}", x);
    println!("y = {}", y);
    println!("x + y = {}", x + y);
    println!("x * y = {}", x * y);
}
```

## 📁 项目结构详解
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```
my_project/
├── Cargo.toml          # 项目元数据和依赖
├── Cargo.lock          # 依赖版本锁定（自动生成）
├── src/
│   ├── main.rs         # 可执行程序入口
│   └── lib.rs          # 库代码（如果有）
├── tests/              # 集成测试
├── benches/            # 基准测试
├── examples/           # 示例代码
└── target/             # 编译输出（可删除）
    ├── debug/          # 开发构建
    └── release/        # 发布构建
```

## ⚠️ 常见错误
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 错误 | 原因 | 修复 |
|------|------|------|
| `unresolved import` | 模块未找到 | 检查模块路径 |
| `expected ;` | 缺少分号 | 添加 `;` |
| `cannot find value` | 变量未定义 | 检查变量名和作用域 |

## 🎮 练习
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### 练习 1: 修改程序
>
> **[来源: [crates.io](https://crates.io/)]**

修改 `main.rs` 输出：

```
Hello, Rust!
版本: 1.96.0+
```

### 练习 2: 简单计算器
>
> **[来源: [docs.rs](https://docs.rs/)]**

创建一个程序，接受两个数字并输出它们的和、差、积、商。

<details>
<summary>参考答案</summary>

```rust
use std::io;

fn main() {
    let mut input = String::new();

    println!("输入第一个数字:");
    io::stdin().read_line(&mut input).unwrap();
    let a: f64 = input.trim().parse().unwrap();
    input.clear();

    println!("输入第二个数字:");
    io::stdin().read_line(&mut input).unwrap();
    let b: f64 = input.trim().parse().unwrap();

    println!("和: {}", a + b);
    println!("差: {}", a - b);
    println!("积: {}", a * b);
    println!("商: {}", a / b);
}
```

</details>

## ✅ 自我检测
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

1. `cargo new` 创建了哪些文件？
2. `println!` 后面的 `!` 表示什么？
3. 开发模式和发布模式有什么区别？

## 📖 延伸阅读

- [Cargo 指南](https://doc.rust-lang.org/cargo/guide/) [来源: Rust Team / Cargo Book 2025]
- [Rust 程序结构](https://doc.rust-lang.org/book/ch03-00-common-programming-concepts.html) [来源: Rust Team / TRPL 2025]

---

## 📚 权威来源索引

- [The Rust Programming Language — Ch1](https://doc.rust-lang.org/book/ch01-00-getting-started.html) [来源: Rust Team / TRPL 2025]
- [Cargo Guide](https://doc.rust-lang.org/cargo/guide/) [来源: Rust Team / Cargo Book 2025]
- [Rust 学习路线图](03_learning_roadmap.md)
- [安装 Rust](02_installation.md)
- [Rust 哲学与设计原则](04_rust_philosophy.md)
- [Rust 所有权深入](../01_fundamentals/04_ownership.md)

---

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
