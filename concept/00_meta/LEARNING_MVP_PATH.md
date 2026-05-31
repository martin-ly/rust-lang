# MVP 学习路径：从零到多线程 CLI（40 小时）

> **受众**: [初学者]
> **Bloom 层级**: 记忆 → 应用
> **定位**: 本项目的**最小可行学习路径**（Minimum Viable Path）。无论背景如何，完成本路径即可独立编写带并发/异步的 Rust CLI 工具。
> **前置依赖**: 无
> **预期产出**: 一个功能完整的多线程/异步命令行工具（如文件搜索器、日志分析器或端口扫描器）
> **总时长**: ~40 小时（可拆分为 2 周，每日 3 小时）

---

## 路径总览

```
Week 1: 基础能力构建（20h）
├─ Day 1-2: Hello World + 基础语法      [4h]
├─ Day 3-4: 所有权与借用                [6h]
├─ Day 5-6: 类型系统与错误处理          [6h]
└─ Day 7:   第一个 CLI 工具（无并发）    [4h]

Week 2: 并发与工程化（20h）
├─ Day 8-9:  集合与迭代器               [4h]
├─ Day 10-11: 多线程与并发              [6h]
├─ Day 12-13: 异步基础                  [6h]
└─ Day 14:   综合项目：多线程/异步 CLI  [4h]
```

---

## Week 1: 基础能力构建

### Day 1-2: Hello World + 基础语法 [4h]

**目标**: 安装 Rust，理解变量、函数、控制流，能编写简单程序。

| 任务 | 内容 | 时长 | 验证标准 |
|:---|:---|:---:|:---|
| 安装 | `rustup` 安装、IDE 配置、Cargo 初识 | 0.5h | `cargo --version` 正常输出 |
| 阅读 | [concept/01_foundation/00_hello_world.md](../01_foundation/00_hello_world.md) | 0.5h | 理解 `fn main` 和 `println!` |
| 阅读 | [concept/01_foundation/02_variables.md](../01_foundation/02_variables.md) | 0.5h | 区分 `let` / `let mut` / `const` |
| 练习 | [exercises/rustlings_style/variables.rs](../../exercises/rustlings_style/variables.rs) | 0.5h | 全部编译通过 |
| 阅读 | [concept/01_foundation/03_control_flow.md](../01_foundation/03_control_flow.md) | 1h | 掌握 `if` / `match` / `for` / `while` |
| 练习 | 编写猜数字游戏（无错误处理版） | 1h | 能运行，可猜测 1-100 的随机数 |

**产出**: `guessing_game_v1.rs` — 基础猜数字游戏

---

### Day 3-4: 所有权与借用 [6h]

**目标**: 理解 Rust 最核心的内存管理规则，能独立解决借用检查器错误。

| 任务 | 内容 | 时长 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/01_foundation/01_ownership.md](../01_foundation/01_ownership.md) | 1.5h | 能向他人解释"所有权三规则" |
| 练习 | [exercises/rustlings_style/move_semantics.rs](../../exercises/rustlings_style/move_semantics.rs) | 1h | 全部编译通过 |
| 阅读 | [concept/01_foundation/02_borrowing.md](../01_foundation/02_borrowing.md) | 1.5h | 区分 `&T` / `&mut T`，理解生命周期标注 |
| 练习 | 修复 5 个编译器借用错误（从错误信息推导修复方案） | 1h | 不使用 `clone()` 或 `Rc` 也能编译 |
| 测验 | 自测：为什么这段代码编译失败？ | 1h | 能说出"同时存在可变和不可变引用" |

**关键概念**: `Ownership` · `Move` · `Borrow` · `Lifetime` · `Dangling Pointer`

**产出**: 一份个人"借用检查器错误速查表"

---

### Day 5-6: 类型系统与错误处理 [6h]

**目标**: 掌握 Rust 的类型系统核心，能用 `Result`/`Option` 处理错误。

| 任务 | 内容 | 时长 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/01_foundation/04_type_system.md](../01_foundation/04_type_system.md) | 1.5h | 区分 `struct` / `enum` / `tuple` |
| 阅读 | [concept/02_intermediate/01_traits.md](../02_intermediate/01_traits.md) | 1.5h | 能为自己定义的 `struct` 实现 `Debug` 和 `Display` |
| 阅读 | [concept/01_foundation/05_error_handling.md](../01_foundation/05_error_handling.md) | 1h | 掌握 `Result` / `Option` / `?` 运算符 |
| 练习 | 重构猜数字游戏：添加输入验证、优雅错误处理 | 1.5h | 输入非数字时不 panic |
| 阅读 | [concept/02_intermediate/02_generics.md](../02_intermediate/02_generics.md) | 0.5h | 理解泛型函数的基本写法 |

**产出**: `guessing_game_v2.rs` — 带错误处理的猜数字游戏

---

### Day 7: 第一个 CLI 工具（无并发） [4h]

**目标**: 综合运用 Week 1 知识，完成一个真实可用的 CLI 程序。

| 任务 | 内容 | 时长 | 验证标准 |
|:---|:---|:---:|:---|
| 项目 | 文件内容搜索器 `rsgrep`：递归搜索目录中的文本 | 2h | `cargo run -- "pattern" ./dir` 能输出匹配行 |
| 扩展 | 添加 `--ignore-case`、`-n` 行号、`-r` 递归选项 | 1.5h | 所有 flag 正常工作 |
| 阅读 | [concept/06_ecosystem/01_toolchain.md](../06_ecosystem/01_toolchain.md)（Cargo 部分） | 0.5h | 理解 `Cargo.toml` 基本结构 |

**产出**: `rsgrep` 项目 — 可发布的 CLI 工具雏形

---

## Week 2: 并发与工程化

### Day 8-9: 集合与迭代器 [4h]

**目标**: 熟练使用 Rust 标准库集合和迭代器，写出惯用代码。

| 任务 | 内容 | 时长 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/02_intermediate/04_collections.md](../02_intermediate/04_collections.md) | 1h | 知道何时用 `Vec` / `HashMap` / `BTreeMap` |
| 练习 | 用迭代器重构 `rsgrep`（消除显式 `for` 循环） | 1h | 代码行数减少 30%+ |
| 阅读 | [concept/02_intermediate/05_iterators.md](../02_intermediate/05_iterators.md) | 1h | 掌握 `map` / `filter` / `fold` / `collect` |
| 练习 | 实现管道操作：读取 → 过滤 → 转换 → 输出 | 1h | 使用 `Iterator` 链式调用 |

**产出**: `rsgrep` v2 — 迭代器驱动的惯用 Rust 代码

---

### Day 10-11: 多线程与并发 [6h]

**目标**: 理解 `Send`/`Sync`，能用 `std::thread` 和通道编写并发程序。

| 任务 | 内容 | 时长 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/03_advanced/01_concurrency.md](../03_advanced/01_concurrency.md) | 2h | 能解释 `Send` 和 `Sync` 的区别 |
| 练习 | 用 `std::thread::spawn` 并行搜索多个目录 | 1.5h | 多线程版本比单线程快 |
| 阅读 | [concept/03_advanced/02_parallelism.md](../03_advanced/02_parallelism.md)（前半部分） | 1h | 理解 `Mutex` / `Arc` 的使用场景 |
| 练习 | 用 `mpsc::channel` 实现生产者-消费者日志处理器 | 1.5h | 多个生产者线程 + 单个消费者线程 |

**产出**: `rsgrep` v3 — 多线程并行搜索版本

---

### Day 12-13: 异步基础 [6h]

**目标**: 理解 `Future`/`async`/`await`，能用 Tokio 编写简单异步程序。

| 任务 | 内容 | 时长 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/03_advanced/02_async.md](../03_advanced/02_async.md)（前半部分） | 2h | 理解 `async fn` 返回 `Future` |
| 环境 | 添加 `tokio = { version = "1", features = ["full"] }` | 0.5h | `cargo build` 成功 |
| 练习 | 用 `tokio::spawn` 并行执行多个 HTTP 请求 | 1.5h | 并发请求总时间 < 串行时间 |
| 阅读 | [concept/03_advanced/02_async_programming.md](../03_advanced/02_async_programming.md)（基础部分） | 1.5h | 理解 `await` 的挂起语义 |
| 练习 | 实现异步文件读取 + 内容搜索 | 0.5h | 使用 `tokio::fs` |

**产出**: 异步 HTTP 客户端工具 `async_fetch`

---

### Day 14: 综合项目：多线程/异步 CLI [4h]

**目标**: 整合两周知识，完成一个可展示的 CLI 项目。

**项目选项**（三选一）：

| 选项 | 描述 | 技术点 |
|:---|:---|:---|
| A. 端口扫描器 | 扫描目标 IP 的开放端口 | `async`/多线程 + 超时 + 错误处理 |
| B. 日志分析器 | 分析日志文件，统计错误频率 | 迭代器 + 并发读取 + 正则匹配 |
| C. 目录对比工具 | 递归对比两个目录的差异 | 多线程遍历 + 哈希比较 + 报告生成 |

**要求**:

- [ ] 使用 `clap` 解析命令行参数
- [ ] 错误处理：所有 I/O 错误优雅处理（不 panic）
- [ ] 并发：至少使用多线程或异步中的一种
- [ ] 测试：包含至少 3 个单元测试
- [ ] 文档：`README.md` 说明用法和安装

**产出**: 一个可 `cargo install` 的完整 CLI 工具

---

## 验证清单（Checkpoint）

完成本路径后，你应该能：

- [ ] **编译**: 独立解决 90% 的编译错误（不求助搜索引擎）
- [ ] **所有权**: 在 30 秒内判断一段代码是否违反借用规则
- [ ] **错误处理**: 在所有 I/O 边界使用 `Result`，不用 `.unwrap()`
- [ ] **并发**: 选择正确的并发原语（`thread` vs `async` vs `channel`）
- [ ] **工具链**: 熟练使用 `cargo` 的 build/test/run/doc/clippy/fmt
- [ ] **生态**: 能在 crates.io 找到并集成合适的第三方库

---

## 扩展路径

完成 MVP 后，可按兴趣选择深入方向：

| 方向 | 下一步文件 | 预估时间 |
|:---|:---|:---:|
| 系统编程 | [concept/03_advanced/03_unsafe.md](../03_advanced/03_unsafe.md) | +20h |
| Web 后端 | [concept/06_ecosystem/03_web_frameworks.md](../06_ecosystem/03_web_frameworks.md) | +20h |
| 嵌入式 | [concept/06_ecosystem/05_embedded.md](../06_ecosystem/05_embedded.md) | +30h |
| 形式化验证 | [concept/04_formal/03_ownership_formal.md](../04_formal/03_ownership_formal.md) | +40h |
| 性能优化 | [concept/03_advanced/04_optimization.md](../03_advanced/04_optimization.md) | +15h |

---

> **文档版本**: 1.0
> **对应 Rust 版本**: 1.96.0 (Edition 2024)
> **最后更新**: 2026-05-30
> **状态**: ✅ MVP 路径已创建
