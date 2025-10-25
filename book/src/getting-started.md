# 快速开始

本页面将帮助你快速上手 Rust 学习系统。

---

## 📋 前置要求

开始学习前，请确保你已经：

1. **安装 Rust**

   ```bash
   curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
   ```

2. **配置开发环境**
   - 推荐使用 VS Code + rust-analyzer 扩展
   - 或者 IntelliJ IDEA + Rust 插件

3. **验证安装**

   ```bash
   rustc --version
   cargo --version
   ```

---

## 🎯 学习路径选择

根据你的背景和目标，选择合适的学习路径：

### 路径一：完全新手

**推荐顺序**:

1. [C01: 所有权、借用与作用域](./c01/README.md)
2. [C02: 类型系统](./c02/README.md)
3. [C03: 控制流与函数](./c03/README.md)

**学习方式**:

- 每天 1-2 小时
- 完成每个模块的所有示例
- 理解每个概念再前进

**预计时间**: 2-3 周

### 路径二：有编程经验

**推荐顺序**:

1. 快速浏览 C01-C03（理解 Rust 特有概念）
2. 深入学习 C04-C06（泛型、并发、异步）
3. 根据需求选择 C07-C14

**学习方式**:

- 重点关注 Rust 与其他语言的差异
- 运行代码示例，理解所有权系统
- 参与实战项目

**预计时间**: 1-2 周

### 路径三：项目驱动

**推荐顺序**:

1. 选择一个[实战项目](./projects/README.md)
2. 遇到问题查阅相关模块
3. 补充基础知识

**学习方式**:

- 边做边学
- 使用搜索功能快速定位
- 参考代码示例

**预计时间**: 根据项目而定

---

## 📚 第一个 Rust 程序

让我们从一个简单的例子开始：

```rust
fn main() {
    println!("Hello, Rust 学习系统！");
    
    // 变量绑定
    let message = "欢迎开始学习";
    println!("{}", message);
    
    // 所有权转移
    let s1 = String::from("Rust");
    let s2 = s1; // s1 所有权转移给 s2
    // println!("{}", s1); // 错误！s1 已失效
    println!("{}", s2); // 正确
}
```

**编译运行**:

```bash
rustc main.rs
./main
```

---

## 🎓 学习建议

### 1. 理解核心概念

Rust 有一些独特的概念，务必深入理解：

- **所有权系统**: Rust 的核心特性
- **借用和引用**: 如何安全地共享数据
- **生命周期**: 引用的有效性
- **模式匹配**: 强大的控制流工具

### 2. 多写代码

每个示例都要亲自运行：

```bash
# 创建新项目
cargo new my_project
cd my_project

# 编辑 src/main.rs
# 运行项目
cargo run

# 运行测试
cargo test
```

### 3. 阅读编译器错误

Rust 编译器会给出详细的错误信息：

```rust
error[E0382]: borrow of moved value: `s1`
  --> src/main.rs:4:20
   |
2  |     let s1 = String::from("hello");
   |         -- move occurs because `s1` has type `String`
3  |     let s2 = s1;
   |              -- value moved here
4  |     println!("{}", s1);
   |                    ^^ value borrowed here after move
```

**学会阅读和理解这些错误，它们是最好的老师！**

### 4. 使用 Clippy

Clippy 是 Rust 的 linter，能给出代码改进建议：

```bash
rustup component add clippy
cargo clippy
```

### 5. 查阅文档

- **标准库文档**: <https://doc.rust-lang.org/std/>
- **Rust Book**: <https://doc.rust-lang.org/book/>
- **本系统搜索**: 使用右上角搜索功能

---

## 🛠️ 开发工具

### VS Code 配置

推荐扩展：

- `rust-analyzer`: Rust 语言服务器
- `crates`: Crate 依赖管理
- `Better TOML`: TOML 文件支持
- `Error Lens`: 内联显示错误

### Cargo 常用命令

```bash
# 创建项目
cargo new project_name
cargo new --lib library_name

# 构建和运行
cargo build
cargo run
cargo build --release

# 测试
cargo test
cargo test test_name

# 检查和 lint
cargo check
cargo clippy

# 格式化
cargo fmt

# 文档
cargo doc --open

# 依赖管理
cargo add package_name
cargo update
```

---

## 📖 下一步

现在你已经准备好了！选择一个起点：

- **系统学习**: [C01: 所有权、借用与作用域](./c01/README.md)
- **查看路线**: [学习路线图](./learning-roadmap.md)
- **直接实战**: [实战项目](./projects/README.md)
- **搜索主题**: 使用右上角搜索功能

---

**准备好了吗？让我们开始吧！** 🚀
