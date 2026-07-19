# 交互式代码示例指南

本指南介绍如何使用本文档中的交互式代码示例功能。

---

## 🎯 功能概览

所有代码示例都集成了 **Rust Playground**，让你可以：

- ✅ 直接在浏览器中运行代码
- ✅ 编辑代码并查看结果
- ✅ 分享你的代码修改
- ✅ 无需本地 Rust 环境

---

## 🚀 如何使用

### 1. 识别可运行代码

在文档中，可运行的代码块会在右上角显示 **"▶ Run"** 按钮：

```rust
fn main() {
    println!("Hello, Rust 学习系统！");
}
```

### 2. 运行代码

点击代码块右上角的 **"▶ Run"** 按钮，代码将在 Rust Playground 中打开并自动运行。

### 3. 编辑和实验

在 Playground 中，你可以：

- **修改代码**: 直接编辑任何部分
- **运行**: 点击 "Run" 查看结果
- **格式化**: 点击 "Format" 美化代码
- **分享**: 点击 "Share" 生成分享链接

### 4. 保存你的工作

Playground 会自动保存你的修改到 URL 中，你可以：

- 收藏页面保存进度
- 复制 URL 分享给他人
- 在多个设备间同步

---

## 📚 示例类型

### 基础示例

简单的独立代码片段，可直接运行：

```rust
fn main() {
    // 这是一个基础示例
    let x = 42;
    println!("答案是: {}", x);
}
```

### 多文件示例

对于需要多个模块的示例，我们会提供完整的代码结构：

```rust
// 主程序
fn main() {
    let user = User::new("Alice", 30);
    println!("{}", user.greet());
}

// 用户结构体
struct User {
    name: String,
    age: u32,
}

impl User {
    fn new(name: &str, age: u32) -> Self {
        User {
            name: name.to_string(),
            age,
        }
    }
    
    fn greet(&self) -> String {
        format!("你好，我是 {}，今年 {} 岁", self.name, self.age)
    }
}
```

### 带依赖的示例

某些高级示例可能需要外部 crate。这些会在 Playground 的 Cargo.toml 中预配置：

```rust,editable
// 示例：使用 serde 进行 JSON 序列化
// 注意：在 Playground 中需要添加依赖
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug)]
struct Person {
    name: String,
    age: u32,
}

fn main() {
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
    };
    
    let json = serde_json::to_string(&person).unwrap();
    println!("JSON: {}", json);
}
```

---

## 💡 学习建议

### 1. 主动实验

不要只是阅读代码，试着：

- 修改变量值
- 添加新的 `println!` 语句
- 尝试不同的实现方式
- 故意引入错误，观察编译器提示

### 2. 理解错误信息

Rust 编译器会给出详细的错误提示：

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;
    println!("{}", s1);  // 尝试运行这段代码
}
```

**练习**: 运行上面的代码，阅读错误信息，理解所有权系统。

### 3. 对比不同方案

尝试多种解决方案，比较它们的优劣：

```rust
// 方案1: 使用 clone()
fn solution1() {
    let s1 = String::from("hello");
    let s2 = s1.clone();
    println!("s1: {}, s2: {}", s1, s2);
}

// 方案2: 使用借用
fn solution2() {
    let s1 = String::from("hello");
    let s2 = &s1;
    println!("s1: {}, s2: {}", s1, s2);
}

fn main() {
    solution1();
    solution2();
}
```

### 4. 构建完整程序

从小示例开始，逐步构建完整的程序：

1. **第一步**: 运行基础示例
2. **第二步**: 添加新功能
3. **第三步**: 处理边界情况
4. **第四步**: 优化和重构

---

## 🎓 高级功能

### 编译模式

Playground 支持多种编译模式：

- **Debug**: 默认模式，编译快，包含调试信息
- **Release**: 优化模式，运行更快
- **ASM**: 查看生成的汇编代码
- **MIR**: 查看中间表示

### Rust 版本

可以选择不同的 Rust 版本：

- **Stable**: 稳定版（推荐）
- **Beta**: 测试版
- **Nightly**: 开发版（某些高级特性需要）

### 代码片段

Playground 支持多种代码片段：

- **Top 100**: 常用代码模式
- **Crates**: 流行的第三方库示例
- **Examples**: Rust Book 示例

---

## 🛠️ 故障排除

### 代码无法运行？

1. **检查语法**: 确保代码语法正确
2. **检查依赖**: 某些示例需要添加 crate 依赖
3. **检查版本**: 某些特性可能需要 nightly 版本

### Playground 加载缓慢？

1. **网络问题**: 确保网络连接正常
2. **浏览器缓存**: 清除浏览器缓存
3. **备选方案**: 复制代码到本地 Rust 环境

### 想保存多个版本？

1. **使用 Gist**: Playground 可以保存到 GitHub Gist
2. **本地备份**: 复制代码到本地文件
3. **浏览器书签**: 保存不同版本的 Playground URL

---

## 📖 相关资源

- [Rust Playground 官网](https://play.rust-lang.org/)
- [Rust Book - 在线版](https://doc.rust-lang.org/book/)
- [Rust By Example](https://doc.rust-lang.org/rust-by-example/)
- [本项目 GitHub](https://github.com/your-username/rust-lang)

---

## 🤝 贡献示例

如果你创建了有价值的示例，欢迎贡献！

### 贡献步骤

1. Fork 本项目
2. 添加你的示例
3. 确保代码可运行
4. 提交 Pull Request

### 示例要求

- ✅ 代码清晰，有注释
- ✅ 可独立运行
- ✅ 展示明确的概念
- ✅ 包含必要的解释

---

**开始探索交互式示例吧！** 🚀

记住：**最好的学习方式就是动手实践！**
