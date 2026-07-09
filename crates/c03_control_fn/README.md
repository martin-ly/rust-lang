# C03: 控制流与函数

> **程序逻辑基础** | **流程控制** | ⭐⭐⭐⭐ 重要性

## 模块职责

本 crate 涵盖 Rust 的控制流和函数系统：

- **条件控制**: `if`, `match`, `if let` 表达式
- **循环控制**: `loop`, `while`, `for`, 迭代器
- **函数定义**: 参数、返回值、高阶函数
- **闭包**: 匿名函数、捕获环境、Fn trait
- **错误处理**: `Result`, `Option`, `?` 运算符

## 目录结构

```text
src/
├── lib.rs              # 模块入口
├── bin/
│   └── main.rs         # CLI 可执行文件
├── control_flow/       # 控制流
├── functions/          # 函数
├── closures/           # 闭包
└── error_handling/     # 错误处理
```

## 主要概念

### 控制流表达式

| 表达式 | 用途 | 特点 |
|--------|------|------|
| `if` | 条件分支 | 返回值的表达式 |
| `match` | 模式匹配 | 穷尽性检查 |
| `if let` | 简化匹配 | 单模式处理 |
| `while let` | 条件循环 | 模式匹配循环 |
| `loop` | 无限循环 | 可带标签退出 |
| `for` | 迭代循环 | 使用 IntoIterator |

### 闭包 Trait

| Trait | 捕获方式 | 调用次数 |
|-------|----------|----------|
| `Fn` | 不可变借用 | 多次 |
| `FnMut` | 可变借用 | 多次 |
| `FnOnce` | 获取所有权 | 一次 |

## 使用示例

### Match 表达式

```rust
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(i32, i32, i32),
}

fn process_message(msg: Message) {
    match msg {
        Message::Quit => println!("退出"),
        Message::Move { x, y } => println!("移动到 ({}, {})", x, y),
        Message::Write(text) => println!("文本: {}", text),
        Message::ChangeColor(r, g, b) => {
            println!("改变颜色到 RGB({}, {}, {})", r, g, b)
        }
    }
}
```

### 闭包

```rust
fn main() {
    let x = 4;

    // 捕获环境变量 x
    let equal_to_x = |z| z == x;

    let y = 4;
    assert!(equal_to_x(y));

    // 使用泛型存储闭包
    let mut operations: Vec<Box<dyn Fn(i32) -> i32>> = vec![
        Box::new(|x| x + 1),
        Box::new(|x| x * 2),
    ];

    for op in &operations {
        println!("{}", op(5));
    }
}
```

### 错误处理

```rust
use std::fs::File;
use std::io::{self, Read};

fn read_username_from_file() -> Result<String, io::Error> {
    let mut file = File::open("hello.txt")?;
    let mut username = String::new();
    file.read_to_string(&mut username)?;
    Ok(username)
}

// 简化版本
fn read_username_from_file_short() -> Result<String, io::Error> {
    std::fs::read_to_string("hello.txt")
}
```

## 依赖关系

### 上游依赖

- `c02_type_system`: 类型系统基础

### 外部依赖

```toml
[dependencies]
tokio = { workspace = true }
tokio-stream = { workspace = true }
serde = { workspace = true }
anyhow = { workspace = true }
thiserror = { workspace = true }
tracing = { workspace = true }
```

## 运行方式

```bash
# 运行测试
cargo test -p c03_control_fn

# 运行 CLI
cargo run -p c03_control_fn

# 运行示例
cargo run -p c03_control_fn --example control_flow_example
```

## 学习路径建议

1. 学习 `match` 表达式的穷尽性检查
2. 理解闭包的三种捕获方式
3. 掌握 `?` 运算符的错误传播
4. 练习迭代器的组合使用

## 形式化验证示例

本 crate 包含 Kani 函数合约与循环不变量示例，详见 [`src/kani_examples.rs`](src/kani_examples.rs)。
这些示例使用 `#[cfg(kani)]` 保护，仅在运行 `cargo kani` 时编译，不影响常规的 `cargo build/test/check`。

| 示例 | 覆盖内容 |
|:---|:---|
| `max_of_two` | 函数后置条件（`#[kani::ensures]`） |
| `count_even_nonnegative_is_exact` | 循环不变量（`#[kani::loop_invariant]`） |
| `checked_div_relation` | 前置条件（`#[kani::requires]`）与符号关系 |
| `verify_linear_search_index_in_bounds` | 下标边界与循环展开（`#[kani::unwind]`） |

相关概念页：

- [Kani：Rust 有界模型检查器](../../concept/04_formal/04_model_checking/32_kani.md)
- [现代 Rust 验证工具生态（2025-2026）](../../concept/04_formal/04_model_checking/22_modern_verification_tools.md)
- [Hoare 逻辑：程序验证的形式化基础与 Rust 契约](../../concept/04_formal/03_operational_semantics/15_hoare_logic.md)

## 相关文档

- [Rust Book - Control Flow](https://doc.rust-lang.org/book/ch03-05-control-flow.html)
- [Rust Book - Closures](https://doc.rust-lang.org/book/ch13-01-closures.html)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.2
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-07-09
**状态**: ✅ 权威来源对齐完成 (Batch 8) · 新增 Kani 形式化验证示例导航
