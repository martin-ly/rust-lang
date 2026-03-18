# Hello, World

> **你的第一个 Rust 程序**
> **预计时间**: 15 分钟

## 🎯 学习目标

完成本章后，你将能够：

- [ ] 使用 Cargo 创建新项目
- [ ] 编写、编译和运行 Rust 程序
- [ ] 理解 Rust 项目结构
- [ ] 使用基本打印宏

## 📋 先决条件

- 已完成 [安装 Rust](installation.md)
- 了解基本的命令行操作

## 🚀 创建项目

### 使用 Cargo 创建

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

### Cargo.toml

```toml
[package]
name = "hello_world"
version = "0.1.0"
edition = "2024"      # Rust 版本

[dependencies]
# 依赖项（目前为空）
```

### src/main.rs

```rust
fn main() {
    println!("Hello, world!");
}
```

## 🏃 编译和运行

### 开发模式（快速编译）

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

```bash
cargo run --release
```

## 🧠 代码解析

### `fn main()`

- Rust 程序的入口点
- 必须是 `fn main()` 函数
- 无参数（简单情况）

### `println!` 宏

```rust
println!("Hello, world!");           // 基本用法
println!("Hello, {}!", "Rust");      // 格式化
println!("1 + 1 = {}", 1 + 1);       // 表达式
```

注意 `!` 表示这是一个**宏**，不是普通函数。

## ✨ 增强示例

### 示例 1: 交互式程序

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

| 错误 | 原因 | 修复 |
|------|------|------|
| `unresolved import` | 模块未找到 | 检查模块路径 |
| `expected ;` | 缺少分号 | 添加 `;` |
| `cannot find value` | 变量未定义 | 检查变量名和作用域 |

## 🎮 练习

### 练习 1: 修改程序

修改 `main.rs` 输出：

```
Hello, Rust!
版本: 1.94.0
```

### 练习 2: 简单计算器

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

1. `cargo new` 创建了哪些文件？
2. `println!` 后面的 `!` 表示什么？
3. 开发模式和发布模式有什么区别？

## 📖 延伸阅读

- [Cargo 指南](https://doc.rust-lang.org/cargo/guide/)
- [Rust 程序结构](https://doc.rust-lang.org/book/ch03-00-common-programming-concepts.html)

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.94.0
**最后更新**: 2026-03-19
