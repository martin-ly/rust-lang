# 🎓 Rust 交互式学习平台 MVP

> **版本**: v1.0  
> **创建日期**: 2025-10-20  
> **状态**: ✅ MVP 完成

---

## 📊 目录

- [🎓 Rust 交互式学习平台 MVP](#-rust-交互式学习平台-mvp)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [简介](#简介)
  - [核心功能](#核心功能)
    - [1. 练习题库系统](#1-练习题库系统)
    - [2. Rust Playground 集成](#2-rust-playground-集成)
    - [3. 进度追踪](#3-进度追踪)
  - [练习题库](#练习题库)
    - [初级练习 (C01-C03)](#初级练习-c01-c03)
      - [C01: 所有权与借用](#c01-所有权与借用)
      - [C06: 异步编程](#c06-异步编程)
  - [Rust Playground集成](#rust-playground集成)
    - [自动生成Playground链接](#自动生成playground链接)
    - [Playground URL格式](#playground-url格式)
    - [示例集成](#示例集成)
  - [使用指南](#使用指南)
    - [1. 开始练习](#1-开始练习)
    - [2. 完成练习](#2-完成练习)
    - [3. 跟踪进度](#3-跟踪进度)
  - [题库结构](#题库结构)
    - [练习元数据](#练习元数据)
    - [难度级别](#难度级别)
    - [练习类型](#练习类型)
  - [进度追踪系统](#进度追踪系统)
    - [本地进度文件](#本地进度文件)
    - [进度可视化](#进度可视化)
  - [API集成](#api集成)
    - [REST API (未来版本)](#rest-api-未来版本)
  - [最佳实践](#最佳实践)
    - [学习建议](#学习建议)
    - [时间管理](#时间管理)
  - [社区功能 (计划中)](#社区功能-计划中)
  - [技术栈](#技术栈)
  - [贡献](#贡献)
    - [贡献流程](#贡献流程)

## 📋 目录

- [简介](#简介)
- [核心功能](#核心功能)
- [练习题库](#练习题库)
- [Rust Playground集成](#rust-playground集成)
- [使用指南](#使用指南)
- [题库结构](#题库结构)

---

## 简介

交互式学习平台MVP为Rust学习项目提供了在线练习和即时反馈功能。通过集成Rust Playground和结构化的练习题库，学习者可以：

- 🎯 完成渐进式编程练习
- ⚡ 在浏览器中即时运行代码
- 📊 跟踪学习进度
- 🔍 获取自动化反馈
- 💡 查看参考答案和解释

---

## 核心功能

### 1. 练习题库系统

```text
├── exercises/
│   ├── c01_ownership/          # 所有权练习
│   │   ├── 01_move_semantics.md
│   │   ├── 02_borrowing.md
│   │   └── 03_lifetimes.md
│   ├── c02_types/              # 类型系统练习
│   │   ├── 01_trait_basics.md
│   │   └── 02_generics.md
│   ├── c05_concurrency/        # 并发练习
│   │   ├── 01_threads.md
│   │   └── 02_channels.md
│   └── c06_async/              # 异步练习
│       ├── 01_async_basics.md
│       └── 02_futures.md
```

### 2. Rust Playground 集成

每个练习都包含：

- 📝 问题描述
- 🎯 学习目标
- 💻 可运行的起始代码
- 🔗 一键跳转到Rust Playground
- ✅ 测试用例
- 💡 提示系统
- 📚 参考答案

### 3. 进度追踪

```rust
// 练习完成状态
pub struct Progress {
    pub module: String,
    pub exercise_id: String,
    pub status: Status,
    pub attempts: u32,
    pub completed_at: Option<DateTime<Utc>>,
}

pub enum Status {
    NotStarted,
    InProgress,
    Completed,
    Mastered,
}
```

---

## 练习题库

### 初级练习 (C01-C03)

#### C01: 所有权与借用

**练习1: 移动语义**:

```markdown
# 练习: 理解移动语义

## 问题描述
完成以下函数，使其能够正确处理所有权转移。

## 起始代码
[在 Playground 中打开](https://play.rust-lang.org/?version=stable&mode=debug&edition=2024&code=...)

\`\`\`rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;
    
    // TODO: 修复编译错误
    // println!("{}", s1);
}
\`\`\`

## 学习目标
- 理解Rust的移动语义
- 掌握所有权转移规则
- 学会使用clone()方法

## 提示
1. 尝试在使用s1之前克隆它
2. 或者使用引用代替所有权转移

## 测试用例
\`\`\`rust
#[test]
fn test_move_semantics() {
    // 测试代码
}
\`\`\`

## 参考答案
<details>
<summary>点击查看答案</summary>

\`\`\`rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1.clone();  // 克隆s1
    println!("{}", s1);    // 现在可以使用s1了
    println!("{}", s2);
}
\`\`\`

**解释**: 使用`clone()`方法创建s1的深拷贝，这样两个变量都拥有各自的数据。
</details>
```

**练习2: 借用规则**:

```markdown
# 练习: 可变借用与不可变借用

## 问题描述
修复以下代码中的借用冲突。

## 起始代码
[在 Playground 中打开](https://play.rust-lang.org/?version=stable&mode=debug&edition=2024&code=...)

\`\`\`rust
fn main() {
    let mut v = vec![1, 2, 3];
    let r1 = &v;
    let r2 = &mut v;  // 错误！
    r2.push(4);
    println!("{:?}", r1);
}
\`\`\`

## 学习目标
- 理解借用规则
- 掌握可变借用与不可变借用的区别
- 学会借用作用域管理

## 提示
1. 可变借用和不可变借用不能同时存在
2. 注意借用的作用域

## 参考答案
<details>
<summary>点击查看答案</summary>

\`\`\`rust
fn main() {
    let mut v = vec![1, 2, 3];
    {
        let r1 = &v;
        println!("{:?}", r1);
    }  // r1作用域结束
    
    let r2 = &mut v;  // 现在可以创建可变借用
    r2.push(4);
    println!("{:?}", v);
}
\`\`\`
</details>
```

#### C06: 异步编程

**练习1: 基础异步函数**:

```markdown
# 练习: 编写你的第一个异步函数

## 问题描述
将同步函数转换为异步函数，使用async/await语法。

## 起始代码
[在 Playground 中打开](https://play.rust-lang.org/?version=stable&mode=debug&edition=2024&code=...)

\`\`\`rust
use tokio;

// TODO: 将此函数转换为异步函数
fn fetch_data() -> String {
    // 模拟网络请求
    std::thread::sleep(std::time::Duration::from_secs(1));
    "Data fetched".to_string()
}

#[tokio::main]
async fn main() {
    let data = fetch_data();
    println!("{}", data);
}
\`\`\`

## 学习目标
- 理解async/await语法
- 掌握异步函数的编写
- 学会使用tokio运行时

## 提示
1. 使用`async`关键字标记函数
2. 使用`await`关键字等待异步操作
3. 使用`tokio::time::sleep`代替`std::thread::sleep`

## 参考答案
<details>
<summary>点击查看答案</summary>

\`\`\`rust
use tokio;

async fn fetch_data() -> String {
    // 使用异步sleep
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    "Data fetched".to_string()
}

#[tokio::main]
async fn main() {
    let data = fetch_data().await;
    println!("{}", data);
}
\`\`\`
</details>
```

---

## Rust Playground集成

### 自动生成Playground链接

我们提供了工具来自动生成Playground链接：

```bash
# 生成练习的Playground链接
cd tools/playground-gen
cargo run -- --exercise exercises/c01_ownership/01_move_semantics.md
```

### Playground URL格式

```text
https://play.rust-lang.org/?version=stable&mode=debug&edition=2024&code={encoded_code}
```

### 示例集成

```markdown
    ## 在线编辑

    点击下面的按钮在Rust Playground中打开此练习：

    [🚀 在Playground中打开](https://play.rust-lang.org/?version=stable&mode=debug&edition=2024&code=fn%20main()%20%7B%0A%20%20%20%20println!(%22Hello%2C%20world!%22)%3B%0A%7D)

    或者扫描二维码：

        ```text
        ┌───────────────────────────────┐
        │  ████ ▄▄▄▄▄ █ ▀▀█ ████  ████ │
        │  ████ █   █ █▄▀▀█▀████  ████ │
        │  ████ █▄▄▄█ █▀▀█ █████  ████ │
        │  ████▄▄▄▄▄▄▄█ ▀ █ █ ▀▄█▄████ │
        │  ████ ▄▄█▄▀▄▀█▀  ▀  ▀▄█▄████ │
        │  ████ ▄▄▄▄▄ █▀ ▀ ▀▀▀▀██ ████ │
        │  ████ █   █ ███▀▀  ▄█▀█ ████ │
        │  ████ █▄▄▄█ █▀ █ ▄▀▀▄▀▀ ████ │
        │  ████▄▄▄▄▄▄▄█▄█▄█▄▄▄▄▄▄█████ │
        └───────────────────────────────┘
        ```

```

---

## 使用指南

### 1. 开始练习

```bash
# 查看所有可用练习
ls exercises/

# 选择一个模块
cd exercises/c01_ownership/

# 阅读练习说明
cat 01_move_semantics.md

# 在Playground中打开
# (点击文档中的链接)
```

### 2. 完成练习

1. 📖 阅读问题描述和学习目标
2. 💻 在Playground中编写代码
3. ▶️ 运行代码测试
4. 🔍 检查编译错误和警告
5. ✅ 通过所有测试用例
6. 💡 查看参考答案和解释

### 3. 跟踪进度

```bash
# 标记练习为完成
cargo run --bin progress-tracker mark-complete c01_ownership 01

# 查看进度
cargo run --bin progress-tracker show-progress

# 生成进度报告
cargo run --bin progress-tracker report
```

---

## 题库结构

### 练习元数据

每个练习包含以下元数据：

```yaml
---
id: c01_01
module: c01_ownership
title: "理解移动语义"
difficulty: beginner
estimated_time: 15
learning_objectives:
  - "理解Rust的移动语义"
  - "掌握所有权转移规则"
  - "学会使用clone()方法"
tags:
  - ownership
  - move-semantics
  - clone
prerequisites:
  - "基本Rust语法"
related_exercises:
  - c01_02
  - c01_03
---
```

### 难度级别

- 🟢 **Beginner** (初级): 基础概念，15-30分钟
- 🟡 **Intermediate** (中级): 复杂场景，30-60分钟
- 🔴 **Advanced** (高级): 深入理解，60-120分钟
- 🟣 **Expert** (专家): 挑战性问题，2+ 小时

### 练习类型

1. **填空题** - 完成缺失的代码
2. **修复题** - 修复有错误的代码
3. **实现题** - 从头实现功能
4. **优化题** - 改进现有代码
5. **调试题** - 找出并修复bug

---

## 进度追踪系统

### 本地进度文件

```toml
# ~/.rust-learning-progress.toml

[progress]
started_at = "2025-10-20T00:00:00Z"
total_exercises = 50
completed = 15
in_progress = 3

[[exercises]]
id = "c01_01"
status = "completed"
completed_at = "2025-10-20T10:30:00Z"
attempts = 2
time_spent_minutes = 25

[[exercises]]
id = "c01_02"
status = "in_progress"
started_at = "2025-10-20T11:00:00Z"
attempts = 1
```

### 进度可视化

```bash
$ cargo run --bin progress-tracker show-progress

📊 学习进度报告
════════════════════════════════════════════════════

总体进度: ████████░░░░░░░░░░ 40% (20/50)

模块进度:
  C01 所有权: ████████████████░░ 80% (8/10)
  C02 类型:   ██████████░░░░░░░░ 50% (5/10)
  C05 并发:   ████░░░░░░░░░░░░░░ 20% (2/10)
  C06 异步:   ██████░░░░░░░░░░░░ 30% (3/10)

最近完成:
  ✅ c01_08 - 生命周期省略 (20分钟前)
  ✅ c02_05 - 关联类型 (1小时前)
  ✅ c05_02 - 通道通信 (3小时前)

建议下一步:
  📌 c01_09 - 高级生命周期
  📌 c02_06 - GATs练习
  📌 c06_01 - async基础
```

---

## API集成

### REST API (未来版本)

```rust
// 获取练习列表
GET /api/exercises?module=c01&difficulty=beginner

// 提交练习
POST /api/exercises/{id}/submit
{
  "code": "fn main() { ... }",
  "test_results": [...]
}

// 获取进度
GET /api/progress
```

---

## 最佳实践

### 学习建议

1. **按顺序完成**: 从简单到复杂
2. **独立思考**: 先尝试自己解决
3. **参考提示**: 卡住时查看提示
4. **理解答案**: 不要只是复制粘贴
5. **反复练习**: 对困难的题目重复练习

### 时间管理

- 🟢 初级练习: 每天 2-3 道
- 🟡 中级练习: 每天 1-2 道
- 🔴 高级练习: 每周 2-3 道

---

## 社区功能 (计划中)

- 📝 **代码审查**: 提交代码获取社区反馈
- 💬 **讨论区**: 与其他学习者交流
- 🏆 **排行榜**: 激励学习动力
- 👨‍🏫 **导师系统**: 经验丰富的开发者指导

---

## 技术栈

- **前端**: Rust + WebAssembly (未来)
- **练习格式**: Markdown + YAML front matter
- **代码运行**: Rust Playground API
- **进度追踪**: 本地TOML文件 / 云端数据库(未来)

---

## 贡献

欢迎贡献新的练习题！请参考 [练习贡献指南](./CONTRIBUTING_EXERCISES.md)。

### 贡献流程

1. Fork项目
2. 创建练习文件
3. 添加测试用例
4. 生成Playground链接
5. 提交Pull Request

---

**版本**: v1.0  
**最后更新**: 2025-10-20  
**维护者**: Rust Learning Community

🎓 **开始你的交互式Rust学习之旅！** ✨
