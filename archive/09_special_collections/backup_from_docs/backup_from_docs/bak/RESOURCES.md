# 📚 Rust 学习资源大全 (Learning Resources)

> **文档定位**: 精选的 Rust 学习资源和工具推荐
> **使用方式**: 根据学习阶段和需求选择合适的资源
> **相关文档**: [README](./README.md) | [学习检查清单](./LEARNING_CHECKLIST.md) | [快速参考](./QUICK_REFERENCE.md)

**最后更新**: 2025-10-19
**适用版本**: Rust 1.90+

---

## 📋 目录

- [📚 Rust 学习资源大全 (Learning Resources)](#-rust-学习资源大全-learning-resources)
  - [📋 目录](#-目录)
  - [官方资源](#官方资源)
    - [核心文档](#核心文档)
      - [The Rust Book (The Book)](#the-rust-book-the-book)
      - [Rust By Example](#rust-by-example)
      - [The Rustonomicon](#the-rustonomicon)
      - [The Cargo Book](#the-cargo-book)
      - [Rust Reference](#rust-reference)
    - [专题文档](#专题文档)
      - [Async Book](#async-book)
      - [Embedded Rust Book](#embedded-rust-book)
      - [WebAssembly Book](#webassembly-book)
  - [在线教程](#在线教程)
    - [互动教程](#互动教程)
      - [Rustlings](#rustlings)
      - [Tour of Rust](#tour-of-rust)
      - [Exercism - Rust Track](#exercism---rust-track)
    - [文字教程](#文字教程)
      - [Rust 程序设计语言（中文版）](#rust-程序设计语言中文版)
      - [Rust 语言圣经（中文）](#rust-语言圣经中文)
      - [Too Many Lists](#too-many-lists)
  - [视频课程](#视频课程)
    - [英文视频](#英文视频)
      - [Rust Programming Course for Beginners (freeCodeCamp)](#rust-programming-course-for-beginners-freecodecamp)
      - [Jon Gjengset's Videos](#jon-gjengsets-videos)
      - [No Boilerplate](#no-boilerplate)
    - [中文视频](#中文视频)
      - [Rust 编程语言入门教程（bilibili）](#rust-编程语言入门教程bilibili)
  - [书籍推荐](#书籍推荐)
    - [入门书籍](#入门书籍)
      - [Programming Rust (2nd Edition)](#programming-rust-2nd-edition)
      - [Rust in Action](#rust-in-action)
    - [进阶书籍](#进阶书籍)
      - [Rust for Rustaceans](#rust-for-rustaceans)
      - [Zero To Production In Rust](#zero-to-production-in-rust)
    - [专题书籍](#专题书籍)
      - [Rust Atomics and Locks](#rust-atomics-and-locks)
      - [Command-Line Rust](#command-line-rust)
  - [练习平台](#练习平台)
    - [算法练习](#算法练习)
      - [LeetCode](#leetcode)
      - [Codewars](#codewars)
      - [Advent of Code](#advent-of-code)
    - [Rust 专属](#rust-专属)
      - [Rust Quiz](#rust-quiz)
  - [开发工具](#开发工具)
    - [IDE/编辑器](#ide编辑器)
      - [VS Code + rust-analyzer](#vs-code--rust-analyzer)
      - [IntelliJ IDEA + IntelliJ Rust](#intellij-idea--intellij-rust)
      - [Neovim/Vim + rust.vim](#neovimvim--rustvim)
    - [调试工具](#调试工具)
      - [rust-gdb / rust-lldb](#rust-gdb--rust-lldb)
      - [cargo-flamegraph](#cargo-flamegraph)
    - [代码质量](#代码质量)
      - [Clippy](#clippy)
      - [rustfmt](#rustfmt)
      - [cargo-audit](#cargo-audit)
      - [cargo-outdated](#cargo-outdated)
    - [性能分析](#性能分析)
      - [cargo-bench](#cargo-bench)
      - [Criterion](#criterion)
      - [perf / valgrind](#perf--valgrind)
  - [社区资源](#社区资源)
    - [论坛和社区](#论坛和社区)
      - [Rust 官方论坛](#rust-官方论坛)
      - [Reddit - r/rust](#reddit---rrust)
      - [Rust 中文社区](#rust-中文社区)
      - [Stack Overflow](#stack-overflow)
    - [即时通讯](#即时通讯)
      - [Discord - Rust Community](#discord---rust-community)
      - [Zulip - Rust Community](#zulip---rust-community)
      - [Telegram 群组](#telegram-群组)
  - [博客文章](#博客文章)
    - [推荐博客](#推荐博客)
      - [The Rust Blog](#the-rust-blog)
      - [This Week in Rust](#this-week-in-rust)
      - [Amos (fasterthanlime)](#amos-fasterthanlime)
      - [boats.gitlab.io](#boatsgitlabio)
    - [系列文章](#系列文章)
      - [Rust 异步编程系列](#rust-异步编程系列)
      - [Rust 宏编程](#rust-宏编程)
  - [开源项目](#开源项目)
    - [学习项目](#学习项目)
      - [RustOS](#rustos)
      - [mini-redis](#mini-redis)
    - [优秀项目](#优秀项目)
      - [Servo](#servo)
      - [ripgrep](#ripgrep)
      - [tokio](#tokio)
  - [Crates 推荐](#crates-推荐)
    - [必备 Crates](#必备-crates)
      - [序列化](#序列化)
      - [错误处理](#错误处理)
      - [异步](#异步)
      - [HTTP/Web](#httpweb)
      - [数据库](#数据库)
      - [CLI](#cli)
      - [日志](#日志)
    - [实用工具](#实用工具)
  - [🎯 学习路径建议](#-学习路径建议)
    - [新手入门 (0-3个月)](#新手入门-0-3个月)
    - [进阶学习 (3-6个月)](#进阶学习-3-6个月)
    - [高级深入 (6-12个月)](#高级深入-6-12个月)
  - [📞 获取帮助](#-获取帮助)
    - [提问前](#提问前)
    - [提问渠道](#提问渠道)
  - [🔗 相关文档](#-相关文档)

---

## 官方资源

### 核心文档

#### The Rust Book (The Book)

- **链接**: [doc.rust-lang.org/book/](https://doc.rust-lang.org/book/)
- **难度**: ⭐ 入门
- **语言**: 英文（有中文翻译）
- **描述**: Rust 官方入门教程，从零开始系统学习 Rust
- **特色**:
  - 深入浅出，循序渐进
  - 涵盖所有核心概念
  - 配有实践项目

#### Rust By Example

- **链接**: [doc.rust-lang.org/rust-by-example/](https://doc.rust-lang.org/rust-by-example/)
- **难度**: ⭐⭐ 初级-中级
- **语言**: 英文（有中文翻译）
- **描述**: 通过可运行的示例学习 Rust
- **特色**:
  - 代码示例丰富
  - 可以在线运行
  - 实践导向

#### The Rustonomicon

- **链接**: [doc.rust-lang.org/nomicon/](https://doc.rust-lang.org/nomicon/)
- **难度**: ⭐⭐⭐⭐⭐ 高级
- **语言**: 英文
- **描述**: Unsafe Rust 和底层细节
- **特色**:
  - 深入内存布局
  - 理解 unsafe 代码
  - 高级主题

#### The Cargo Book

- **链接**: [doc.rust-lang.org/cargo/](https://doc.rust-lang.org/cargo/)
- **难度**: ⭐⭐ 初级-中级
- **语言**: 英文
- **描述**: Cargo 包管理器完整指南
- **特色**:
  - 项目管理
  - 依赖管理
  - 发布流程

#### Rust Reference

- **链接**: [doc.rust-lang.org/reference/](https://doc.rust-lang.org/reference/)
- **难度**: ⭐⭐⭐ 中级-高级
- **语言**: 英文
- **描述**: Rust 语言规范参考
- **特色**:
  - 详细的语言规范
  - 完整的语法说明
  - 技术细节

### 专题文档

#### Async Book

- **链接**: [rust-lang.github.io/async-book/](https://rust-lang.github.io/async-book/)
- **难度**: ⭐⭐⭐ 中级
- **描述**: 异步编程完整指南

#### Embedded Rust Book

- **链接**: [docs.rust-embedded.org/book/](https://docs.rust-embedded.org/book/)
- **难度**: ⭐⭐⭐⭐ 高级
- **描述**: 嵌入式 Rust 开发

#### WebAssembly Book

- **链接**: [rustwasm.github.io/docs/book/](https://rustwasm.github.io/docs/book/)
- **难度**: ⭐⭐⭐ 中级-高级
- **描述**: Rust 和 WebAssembly

---

## 在线教程

### 互动教程

#### Rustlings

- **链接**: [github.com/rust-lang/rustlings](https://github.com/rust-lang/rustlings)
- **难度**: ⭐⭐ 初级
- **描述**: 小型练习题集，通过修复编译错误学习
- **特色**:
  - 从简单到复杂
  - 即时反馈
  - 本地运行

#### Tour of Rust

- **链接**: [tourofrust.com](https://tourofrust.com/)
- **难度**: ⭐ 入门
- **语言**: 多语言（包括中文）
- **描述**: 交互式 Rust 入门教程
- **特色**:
  - 可在线运行代码
  - 简短的章节
  - 循序渐进

#### Exercism - Rust Track

- **链接**: [exercism.org/tracks/rust](https://exercism.org/tracks/rust)
- **难度**: ⭐⭐⭐ 初级-中级
- **描述**: 编程练习平台，有导师点评
- **特色**:
  - 100+ 练习题
  - 社区反馈
  - 学习路径

### 文字教程

#### Rust 程序设计语言（中文版）

- **链接**: [kaisery.github.io/trpl-zh-cn/](https://kaisery.github.io/trpl-zh-cn/)
- **难度**: ⭐ 入门
- **语言**: 中文
- **描述**: The Rust Book 中文翻译

#### Rust 语言圣经（中文）

- **链接**: [course.rs](https://course.rs/)
- **难度**: ⭐⭐ 初级-中级
- **语言**: 中文
- **描述**: 全面的 Rust 中文教程
- **特色**:
  - 内容详实
  - 中文友好
  - 实战导向

#### Too Many Lists

- **链接**: [rust-unofficial.github.io/too-many-lists/](https://rust-unofficial.github.io/too-many-lists/)
- **难度**: ⭐⭐⭐⭐ 高级
- **描述**: 通过实现链表深入理解 Rust
- **特色**:
  - 深入所有权
  - 理解 unsafe
  - 挑战性强

---

## 视频课程

### 英文视频

#### Rust Programming Course for Beginners (freeCodeCamp)

- **平台**: YouTube
- **难度**: ⭐ 入门
- **时长**: ~10 小时
- **描述**: 从零开始的完整入门课程

#### Jon Gjengset's Videos

- **链接**: [youtube.com/@jonhoo](https://www.youtube.com/@jonhoo)
- **难度**: ⭐⭐⭐⭐ 高级
- **描述**: 深入 Rust 内部机制
- **推荐视频**:
  - "Crust of Rust" 系列
  - "Decrusting" 系列

#### No Boilerplate

- **链接**: [youtube.com/@NoBoilerplate](https://www.youtube.com/@NoBoilerplate)
- **难度**: ⭐⭐ 初级-中级
- **描述**: 简短精炼的 Rust 主题视频

### 中文视频

#### Rust 编程语言入门教程（bilibili）

- **平台**: bilibili
- **难度**: ⭐ 入门
- **描述**: 中文入门教程

---

## 书籍推荐

### 入门书籍

#### Programming Rust (2nd Edition)

- **作者**: Jim Blandy, Jason Orendorff, Leonora F. S. Tindall
- **难度**: ⭐⭐ 初级-中级
- **描述**: O'Reilly 出版的 Rust 综合指南
- **适合**: 有编程经验的初学者

#### Rust in Action

- **作者**: Tim McNamara
- **难度**: ⭐⭐ 初级-中级
- **描述**: 实战导向的 Rust 学习
- **适合**: 喜欢动手实践的学习者

### 进阶书籍

#### Rust for Rustaceans

- **作者**: Jon Gjengset
- **难度**: ⭐⭐⭐⭐ 高级
- **描述**: 高级 Rust 编程技巧和最佳实践
- **适合**: 有一定 Rust 基础的开发者

#### Zero To Production In Rust

- **作者**: Luca Palmieri
- **难度**: ⭐⭐⭐ 中级-高级
- **描述**: 构建生产级后端应用
- **适合**: Web 开发者

### 专题书籍

#### Rust Atomics and Locks

- **作者**: Mara Bos
- **难度**: ⭐⭐⭐⭐ 高级
- **描述**: 深入并发和底层原子操作

#### Command-Line Rust

- **作者**: Ken Youens-Clark
- **难度**: ⭐⭐ 初级-中级
- **描述**: 构建 CLI 工具

---

## 练习平台

### 算法练习

#### LeetCode

- **链接**: [leetcode.com](https://leetcode.com/)
- **描述**: 支持 Rust 的算法题库
- **特色**: 大量题目，面试导向

#### Codewars

- **链接**: [codewars.com](https://www.codewars.com/)
- **描述**: 游戏化的编程练习
- **特色**: 社区解答，难度分级

#### Advent of Code

- **链接**: [adventofcode.com](https://adventofcode.com/)
- **描述**: 每年12月的编程挑战
- **特色**: 有趣的谜题，社区活跃

### Rust 专属

#### Rust Quiz

- **链接**: [dtolnay.github.io/rust-quiz/](https://dtolnay.github.io/rust-quiz/)
- **难度**: ⭐⭐⭐⭐ 高级
- **描述**: Rust 语言细节测试
- **特色**: 挑战理解深度

---

## 开发工具

### IDE/编辑器

#### VS Code + rust-analyzer

- **推荐度**: ⭐⭐⭐⭐⭐
- **描述**: 最流行的 Rust 开发环境
- **插件**:
  - rust-analyzer (必备)
  - crates (依赖管理)
  - Error Lens (错误提示)
  - CodeLLDB (调试)

#### IntelliJ IDEA + IntelliJ Rust

- **推荐度**: ⭐⭐⭐⭐
- **描述**: JetBrains 出品，功能强大
- **特色**: 智能重构，优秀的补全

#### Neovim/Vim + rust.vim

- **推荐度**: ⭐⭐⭐
- **描述**: 轻量级，适合 Vim 用户
- **配置**: 需要配置 LSP

### 调试工具

#### rust-gdb / rust-lldb

- **描述**: Rust 专用调试器
- **用途**: 命令行调试

#### cargo-flamegraph

- **链接**: [github.com/flamegraph-rs/flamegraph](https://github.com/flamegraph-rs/flamegraph)
- **描述**: 性能火焰图
- **安装**: `cargo install flamegraph`

### 代码质量

#### Clippy

- **描述**: Rust 官方 linter
- **安装**: `rustup component add clippy`
- **使用**: `cargo clippy`

#### rustfmt

- **描述**: 代码格式化工具
- **安装**: `rustup component add rustfmt`
- **使用**: `cargo fmt`

#### cargo-audit

- **描述**: 安全漏洞检查
- **安装**: `cargo install cargo-audit`
- **使用**: `cargo audit`

#### cargo-outdated

- **描述**: 检查过时依赖
- **安装**: `cargo install cargo-outdated`
- **使用**: `cargo outdated`

### 性能分析

#### cargo-bench

- **描述**: 基准测试（内置）
- **使用**: `cargo bench`

#### Criterion

- **链接**: [github.com/bheisler/criterion.rs](https://github.com/bheisler/criterion.rs)
- **描述**: 高级基准测试框架

#### perf / valgrind

- **描述**: 系统级性能分析工具
- **用途**: 深度性能分析

---

## 社区资源

### 论坛和社区

#### Rust 官方论坛

- **链接**: [users.rust-lang.org](https://users.rust-lang.org/)
- **描述**: 官方讨论区，新手友好

#### Reddit - r/rust

- **链接**: [reddit.com/r/rust](https://www.reddit.com/r/rust/)
- **描述**: Rust 社区讨论

#### Rust 中文社区

- **链接**: [rustcc.cn](https://rustcc.cn/)
- **描述**: 中文 Rust 社区

#### Stack Overflow

- **链接**: [stackoverflow.com/questions/tagged/rust](https://stackoverflow.com/questions/tagged/rust)
- **描述**: 技术问答平台

### 即时通讯

#### Discord - Rust Community

- **链接**: [discord.gg/rust-lang](https://discord.gg/rust-lang)
- **描述**: 官方 Discord 服务器

#### Zulip - Rust Community

- **链接**: [rust-lang.zulipchat.com](https://rust-lang.zulipchat.com/)
- **描述**: Rust 开发者交流

#### Telegram 群组

- **描述**: 多个 Rust 学习群组

---

## 博客文章

### 推荐博客

#### The Rust Blog

- **链接**: [blog.rust-lang.org](https://blog.rust-lang.org/)
- **描述**: Rust 官方博客，发布公告和新闻

#### This Week in Rust

- **链接**: [this-week-in-rust.org](https://this-week-in-rust.org/)
- **描述**: 每周 Rust 新闻和资源汇总

#### Amos (fasterthanlime)

- **链接**: [fasterthanli.me](https://fasterthanli.me/)
- **描述**: 深度技术文章，讲解透彻

#### boats.gitlab.io

- **链接**: [without.boats](https://without.boats/)
- **描述**: Rust 核心团队成员博客

### 系列文章

#### Rust 异步编程系列

- **作者**: tokio.rs
- **链接**: [tokio.rs/tokio/tutorial](https://tokio.rs/tokio/tutorial)

#### Rust 宏编程

- **The Little Book of Rust Macros**
- **链接**: [danielkeep.github.io/tlborm/](https://danielkeep.github.io/tlborm/)

---

## 开源项目

### 学习项目

#### RustOS

- **链接**: [github.com/rust-embedded/rust-raspberrypi-OS-tutorials](https://github.com/rust-embedded/rust-raspberrypi-OS-tutorials)
- **难度**: ⭐⭐⭐⭐⭐ 高级
- **描述**: 用 Rust 编写操作系统

#### mini-redis

- **链接**: [github.com/tokio-rs/mini-redis](https://github.com/tokio-rs/mini-redis)
- **难度**: ⭐⭐⭐ 中级
- **描述**: Redis 的简化实现，学习异步

### 优秀项目

#### Servo

- **链接**: [github.com/servo/servo](https://github.com/servo/servo)
- **描述**: 实验性浏览器引擎

#### ripgrep

- **链接**: [github.com/BurntSushi/ripgrep](https://github.com/BurntSushi/ripgrep)
- **描述**: 高性能搜索工具

#### tokio

- **链接**: [github.com/tokio-rs/tokio](https://github.com/tokio-rs/tokio)
- **描述**: 异步运行时

---

## Crates 推荐

### 必备 Crates

#### 序列化

```toml
[dependencies]
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
toml = "0.8"
```

#### 错误处理

```toml
[dependencies]
anyhow = "1.0"      # 应用程序
thiserror = "1.0"   # 库
```

#### 异步

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
async-std = "1.0"
futures = "0.3"
```

#### HTTP/Web

```toml
[dependencies]
reqwest = "0.11"    # HTTP 客户端
axum = "0.7"        # Web 框架
actix-web = "4.0"   # Web 框架
```

#### 数据库

```toml
[dependencies]
sqlx = "0.7"        # 异步 SQL
diesel = "2.0"      # ORM
```

#### CLI

```toml
[dependencies]
clap = { version = "4.0", features = ["derive"] }
colored = "2.0"
indicatif = "0.17"
```

#### 日志

```toml
[dependencies]
tracing = "0.1"
tracing-subscriber = "0.3"
log = "0.4"
env_logger = "0.11"
```

### 实用工具

```toml
[dependencies]
# 日期时间
chrono = "0.4"

# 随机数
rand = "0.8"

# 正则表达式
regex = "1.0"

# UUID
uuid = { version = "1.0", features = ["v4"] }

# 并发
rayon = "1.0"      # 数据并行
crossbeam = "0.8"  # 并发工具
```

---

## 🎯 学习路径建议

### 新手入门 (0-3个月)

1. **官方资源**: The Rust Book + Rust By Example
2. **练习**: Rustlings
3. **项目**: 实现简单 CLI 工具

### 进阶学习 (3-6个月)

1. **书籍**: Programming Rust
2. **专题**: Async Book, 并发编程
3. **项目**: Web 应用，异步服务

### 高级深入 (6-12个月)

1. **书籍**: Rust for Rustaceans, Rust Atomics
2. **源码**: 阅读知名项目源码
3. **贡献**: 参与开源项目

---

## 📞 获取帮助

### 提问前

1. **搜索文档**: 先查阅官方文档
2. **搜索已有问题**: Stack Overflow, GitHub Issues
3. **准备 MCVE**: 最小可复现示例

### 提问渠道

- **初学者问题**: Rust 论坛，Discord
- **技术问题**: Stack Overflow
- **Bug 报告**: GitHub Issues

---

## 🔗 相关文档

- **学习检查清单**: [LEARNING_CHECKLIST.md](./LEARNING_CHECKLIST.md)
- **快速参考**: [QUICK_REFERENCE.md](./QUICK_REFERENCE.md)
- **故障排查**: [TROUBLESHOOTING.md](./TROUBLESHOOTING.md)
- **最佳实践**: [BEST_PRACTICES.md](./BEST_PRACTICES.md)

---

**开始你的 Rust 学习之旅！** 🚀

资源虽多，重在坚持。选择适合自己的资源，循序渐进地学习。

**最后更新**: 2025-10-19
**维护团队**: Rust 学习社区
**版本**: v1.0
