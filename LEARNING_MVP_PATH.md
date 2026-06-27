# Rust 最小可行学习路径（MVP Path）

> **目标受众**: [初学者]
> **预计耗时**: 35–45 小时（按每天 2 小时，约 3 周完成）
> **路径终点**: 独立编写一个多线程命令行工具（CLI）
> **设计原则**: 每个阶段必须有可运行的代码，每个概念必须有对应的练习验证
> **标记说明**：
>
> - **`[必修]`** (Required)：必须完成。跳过将导致后续内容无法理解或项目无法完成。
> - **`[推荐]`** (Recommended)：强烈建议完成。跳过不影响核心目标，但会削弱理解深度。
> - **`[选修]`** (Optional)：扩展内容。适合学有余力或希望深入特定方向的读者。

---

## 📑 路径概览

```text
Week 1: Rust 基础与所有权系统（12h）[必修]
    ├─ 第 1 天：Hello World + 工具链（2h）[必修]
    ├─ 第 2 天：所有权与移动语义（2h）[必修]
    ├─ 第 3 天：借用与引用（2h）[必修]
    ├─ 第 4 天：基本类型与集合（2h）[必修]
    └─ 第 5–6 天：综合练习 + Checkpoint（4h）[必修]

Week 2: 类型系统与错误处理（12h）[必修]
    ├─ 第 7 天：结构体、枚举与模式匹配（2h）[必修]
    ├─ 第 8 天：Trait 与泛型入门（2h）[必修]
    ├─ 第 9 天：错误处理（2h）[必修]
    ├─ 第 10 天：模块与 Cargo（2h）[必修]
    └─ 第 11–12 天：综合练习 + Checkpoint（4h）[必修]

Week 3: 并发与 CLI 项目（12h）[必修]
    ├─ 第 13 天：迭代器与闭包（2h）[必修]
    ├─ 第 14 天：多线程基础（2h）[必修]
    ├─ 第 15–16 天：CLI 项目实战（4h）[必修]
    ├─ 第 17 天：代码审查与优化（2h）[推荐]
    └─ 第 18 天：最终 Checkpoint + 扩展路径（2h）[推荐]
```

> **为什么要学所有权？** 所有权是 Rust 最独特、最核心的概念，也是后续所有安全保证的基础。
> Week 1 的投入将在 Week 3 的并发编程中获得十倍回报——无需担心数据竞争。

---

## Week 1：Rust 基础与所有权系统（12h）

### 第 1 天：Hello World + 工具链（2h）`[必修]`

**学习目标**：安装 Rust，运行第一个程序，理解 Cargo 基本操作。

| 任务 | 内容 | 预计时间 | 验证标准 |
| :--- | :--- | :---: | :--- |
| 安装 | `rustup` 安装，配置 VS Code + rust-analyzer | 30min | `rustc --version` 输出 1.96+ |
| 阅读 | [concept/01_foundation/00_start](./concept/01_foundation/00_start.md) | 20min | — |
| 代码 | 运行 `cargo new hello` 并修改打印内容 | 15min | 程序成功运行 |
| 阅读 | [concept/01_foundation/01_ownership.md](./concept/01_foundation/01_ownership.md) 第 1–3 节 | 30min | 能解释 "move" 和 "Copy" 的区别 |
| 练习 | [exercises/src/ownership_borrowing/ex01_hello_move.rs](./exercises/src/ownership_borrowing/) | 25min | 测试通过 |

**Checkpoint 1**（口头自测）：

1. `let x = 5; let y = x;` 之后 `x` 还能用吗？为什么？
2. `let s = String::from("hi"); let s2 = s;` 之后 `s` 还能用吗？为什么？
3. `cargo build` 和 `cargo run` 的区别是什么？

---

### 第 2 天：所有权与移动语义（2h）`[必修]`

**学习目标**：深入理解所有权三规则、Drop 语义、`Clone` 与 `Copy`。

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/01_foundation/01_ownership.md](./concept/01_foundation/01_ownership.md) 第 4–7 节 | 40min | — |
| 代码 | [crates/c01_ownership_borrow_scope](./crates/c01_ownership_borrow_scope/) 运行 ownership 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/src/ownership_borrowing/ex02_move_clone.rs](./exercises/src/ownership_borrowing/) | 30min | 测试通过 |
| 测验 | 完成 [01_ownership.md 嵌入式测验 1–3](./concept/01_foundation/01_ownership.md#嵌入式测验) | 20min | 全部答对 |

---

### 第 3 天：借用与引用（2h）`[必修]`

**学习目标**：掌握不可变借用 `&T`、可变借用 `&mut T`、借用规则。

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/01_foundation/02_borrowing.md](./concept/01_foundation/02_borrowing.md) | 45min | — |
| 代码 | [crates/c01_ownership_borrow_scope](./crates/c01_ownership_borrow_scope/) 运行 borrowing 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/src/ownership_borrowing/ex03_borrowing_rules.rs](./exercises/src/ownership_borrowing/) | 30min | 测试通过 |
| 测验 | 完成 [02_borrowing.md 嵌入式测验 1–3](./concept/01_foundation/02_borrowing.md#嵌入式测验) | 15min | 全部答对 |

---

### 第 4 天：基本类型与集合（2h）`[必修]`

**学习目标**：理解 Rust 的类型系统基础，掌握 Vec、HashMap 的基本用法。

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/01_foundation/04_type_system.md](./concept/01_foundation/04_type_system.md) 第 1–4 节 | 35min | — |
| 阅读 | [concept/01_foundation/08_collections.md](./concept/01_foundation/08_collections.md) 第 1–3 节 | 25min | — |
| 代码 | [crates/c02_type_system](./crates/c02_type_system/) 运行 collections 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/src/type_system/ex01_basic_types.rs](./exercises/src/type_system/) | 30min | 测试通过 |

---

### 第 5–6 天：Week 1 综合练习 + Checkpoint（4h）`[必修]`

**综合项目**：实现一个简单的文本统计工具 `wordcount`

**功能要求**：

- 读取命令行传入的文件路径
- 统计行数、单词数、字符数
- 使用 `Vec` 存储每行内容
- 正确处理文件不存在的情况（初步使用 `panic!` 或 `expect`）

**验证标准**：

- `cargo run -- file.txt` 正确输出统计结果
- 文件不存在时给出清晰错误信息
- 代码通过 `cargo check` 无警告

**Week 1 Checkpoint**（书面自测）：

1. 画出以下代码的所有权转移图：`let s = String::from("a"); let s2 = s; println!("{}", s2);`
2. 为什么 Rust 不允许同时存在可变借用和不可变借用？
3. `Vec::push` 需要什么类型的借用？为什么？

---

## Week 2：类型系统与错误处理（12h）

### 第 7 天：结构体、枚举与模式匹配（2h）`[必修]`

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/01_foundation/04_type_system.md](./concept/01_foundation/04_type_system.md) 第 5–7 节（struct/enum/match） | 40min | — |
| 代码 | [crates/c02_type_system](./crates/c02_type_system/) 运行 enum_pattern 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/src/type_system/ex02_enum_match.rs](./exercises/src/type_system/) | 30min | 测试通过 |
| 小项目 | 为 `wordcount` 添加 `--lines-only`、`--words-only` 选项（使用 enum） | 20min | 功能正确 |

---

### 第 8 天：Trait 与泛型入门（2h）`[必修]`

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/02_intermediate/01_traits.md](./concept/02_intermediate/01_traits.md) 第 1–4 节 | 35min | — |
| 阅读 | [concept/02_intermediate/02_generics.md](./concept/02_intermediate/02_generics.md) 第 1–3 节 | 25min | — |
| 代码 | [crates/c04_generic](./crates/c04_generic/) 运行 trait_basics 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/src/generics_traits/ex01_basic_trait.rs](./exercises/src/generics_traits/) | 30min | 测试通过 |

---

### 第 9 天：错误处理（2h）`[必修]`

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/01_foundation/10_error_handling_basics.md](./concept/01_foundation/10_error_handling_basics.md) | 40min | — |
| 代码 | [crates/c03_control_fn](./crates/c03_control_fn/) 运行 error_handling 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/src/error_handling/ex01_result_option.rs](./exercises/src/error_handling/) | 30min | 测试通过 |
| 重构 | 将 `wordcount` 的 `expect` 改为 `Result` 传播（使用 `?`） | 20min | 功能正确，无 panic |

---

### 第 10 天：模块与 Cargo（2h）`[必修]`

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/02_intermediate/10_module_system.md](./concept/02_intermediate/10_module_system.md) 第 1–3 节 | 30min | — |
| 代码 | 将 `wordcount` 拆分为 `lib.rs`（逻辑）和 `main.rs`（CLI） | 40min | `cargo test` 通过 |
| 练习 | [exercises/src/type_system/ex03_module_split.rs](./exercises/src/type_system/) | 30min | 测试通过 |
| 阅读 | [Cargo 工作区指南](./docs/03_guides/) | 20min | 理解 workspace 概念 |

---

### 第 11–12 天：Week 2 综合练习 + Checkpoint（4h）`[必修]`

**综合项目**：扩展 `wordcount` 为 `texttool`

**新增功能**：

- `--search <pattern>`：在文件中搜索模式（返回匹配行号）
- `--replace <old> <new>`：替换文本并输出到新文件
- 使用 `Result` 统一错误处理
- 使用 `struct Config` 管理命令行参数

**验证标准**：

- 所有功能通过 `cargo test` 测试
- 使用 `clap`（可选）或手动解析参数
- 错误信息清晰，不 panic

**Week 2 Checkpoint**（书面自测）：

1. `Result<T, E>` 和 `Option<T>` 的区别和使用场景？
2. 什么情况下需要给函数添加泛型参数 `<T>`？
3. `mod`、`use`、`pub` 三者分别控制什么？

---

## Week 3：并发与 CLI 项目（12h）

### 第 13 天：迭代器与闭包（2h）`[必修]`

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/01_foundation/15_closure_basics.md](./concept/01_foundation/15_closure_basics.md) | 30min | — |
| 阅读 | [concept/02_intermediate/15_iterator_patterns.md](./concept/02_intermediate/15_iterator_patterns.md) 第 1–3 节 | 30min | — |
| 代码 | [crates/c03_control_fn](./crates/c03_control_fn/) 运行 iterator_closure 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/rustlings_style/ex09_iterator_consumer](./exercises/rustlings_style/ex09_iterator_consumer/) | 30min | 测试通过 |

---

### 第 14 天：多线程基础（2h）`[必修]`

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/03_advanced/01_concurrency.md](./concept/03_advanced/01_concurrency.md) 第 1–4 节 | 40min | — |
| 代码 | [crates/c05_threads](./crates/c05_threads/) 运行 spawn_join 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/src/concurrency/ex01_spawn_join.rs](./exercises/src/concurrency/) | 30min | 测试通过 |
| 关键理解 | 为什么 `move` 闭包在线程中必要？ | 20min | 能用自己的话解释 |

---

### 第 15–16 天：多线程 CLI 项目实战（4h）`[必修]`

**项目目标**：`fastwc` — 多线程文件统计工具

**核心要求**：

- 接受多个文件路径作为参数
- 使用多线程并行处理每个文件
- 使用 `mpsc` 通道收集结果
- 使用 `Arc<Mutex<HashMap>>` 或 `crossbeam::channel` 汇总统计
- 正确处理线程 panic（使用 `join()`）

**代码结构建议**：

```rust
// lib.rs
pub fn process_files(paths: Vec<&str>) -> Result<Vec<FileStats>, Box<dyn Error>> {
    // 1. 为每个文件 spawn 一个线程
    // 2. 通过 channel 发送统计结果
    // 3. 主线程收集并排序输出
}

// main.rs
fn main() -> Result<(), Box<dyn Error>> {
    let args = std::env::args().collect::<Vec<_>>();
    let stats = process_files(&args[1..])?;
    print_stats(&stats);
    Ok(())
}
```

**验证标准**：

- `cargo run -- file1.txt file2.txt file3.txt` 正确输出每个文件的统计
- 处理 10 个 1MB 文件时比单线程版本快（使用 `time` 测量）
- 任意文件不存在时，其他文件仍被处理，最终汇总错误信息
- `cargo test` 全部通过（包含并发测试）

---

### 第 17 天：代码审查与优化（2h）`[推荐]`

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 审查 | 使用 `cargo clippy` 检查 `fastwc` | 15min | 0 warning |
| 优化 | 使用 `BufReader` 替代逐行 `read_to_string` | 30min | 性能提升可见 |
| 文档 | 为 `lib.rs` 添加 doc comments | 30min | `cargo doc` 生成清晰文档 |
| 测试 | 使用 `tempfile` crate 编写集成测试 | 45min | 测试覆盖主要路径 |

---

### 第 18 天：最终 Checkpoint + 扩展路径（2h）`[推荐]`

**最终 Checkpoint**（项目级评估）：

1. 向同伴（或录音）解释：`fastwc` 为什么不会有数据竞争？
2. 如果要在 `fastwc` 中使用 `crossbeam::channel` 替代 `mpsc`，需要改哪些代码？
3. 画出 `fastwc` 的线程 + 通道数据流图。

**扩展路径选择**（根据兴趣选一个方向）：

| 方向 | 下一步 | 核心文件 | 预计时间 |
|:---|:---|:---|:---:|
| **系统编程** | 学习 Unsafe + FFI，尝试调用 C 库 | [Unsafe Rust](./concept/03_advanced/03_unsafe.md) · [FFI](./concept/03_advanced/05_rust_ffi.md) · [内联汇编](./concept/03_advanced/13_inline_assembly.md) | +20h `[选修]` |
| **Web 后端** | 学习 Axum/Tokio，将 `fastwc` 改为 Web 服务 | [Async/Await](./concept/03_advanced/02_async.md) · [网络编程](./concept/03_advanced/18_network_programming.md) | +20h `[选修]` |
| **嵌入式** | 学习 `no_std`，在 microcontroller 上运行 Rust | [嵌入式 Rust](./concept/06_ecosystem/17_embedded_rust.md) · [嵌入式系统](./concept/06_ecosystem/22_embedded_systems.md) | +30h `[选修]` |
| **形式化验证** | 理解所有权证明，使用 Kani/Verus | [RustBelt](./concept/04_formal/04_rustbelt.md) · [验证工具生态](./concept/04_formal/22_modern_verification_tools.md) | +40h `[选修]` |
| **编译器开发** | 理解借用检查器演进，尝试 Miri/BSan | [NLL 与 Polonius](./concept/03_advanced/08_nll_and_polonius.md) · [BorrowSanitizer](./concept/07_future/borrow_sanitizer.md) | +30h `[选修]` |
| **开源贡献** | 为 rust-lang/rust 或 tokio 提交文档 PR | [Rust 版本跟踪](./concept/07_future/05_rust_version_tracking.md) · [Edition 机制](./concept/07_future/22_edition_guide.md) | 持续 `[选修]` |

---

## 配套资源索引

### 概念文件（按阅读顺序）

| 阶段 | 文件 | 预计阅读 |
|:---|:---|:---:|
| W1D1 | [00_start](./concept/01_foundation/00_start.md) | 20min |
| W1D1–2 | [01_ownership](./concept/01_foundation/01_ownership.md) | 70min |
| W1D3 | [02_borrowing](./concept/01_foundation/02_borrowing.md) | 45min |
| W1D4 | [04_type_system](./concept/01_foundation/04_type_system.md) | 35min |
| W1D4 | [08_collections](./concept/01_foundation/08_collections.md) | 25min |
| W2D1 | [04_type_system](./concept/01_foundation/04_type_system.md)（续） | 40min |
| W2D2 | [01_traits](./concept/02_intermediate/01_traits.md) | 35min |
| W2D2 | [02_generics](./concept/02_intermediate/02_generics.md) | 25min |
| W2D3 | [10_error_handling_basics](./concept/01_foundation/10_error_handling_basics.md) | 40min |
| W2D4 | [10_module_system](./concept/02_intermediate/10_module_system.md) | 30min |
| W3D1 | [15_closure_basics](./concept/01_foundation/15_closure_basics.md) | 30min |
| W3D1 | [15_iterator_patterns](./concept/02_intermediate/15_iterator_patterns.md) | 30min |
| W3D2 | [01_concurrency](./concept/03_advanced/01_concurrency.md) | 40min |

### Crate 示例（按运行顺序）

| 阶段 | Crate | 内容 |
|:---|:---|:---|
| W1D2 | [c01_ownership_borrow_scope](./crates/c01_ownership_borrow_scope/) | 所有权、移动、Clone、Drop |
| W1D3 | [c01_ownership_borrow_scope](./crates/c01_ownership_borrow_scope/) | 借用、引用、NLL |
| W1D4 | [c02_type_system](./crates/c02_type_system/) | 集合、基本类型 |
| W2D2 | [c04_generic](./crates/c04_generic/) | Trait、泛型 |
| W2D3 | [c03_control_fn](./crates/c03_control_fn/) | 错误处理 |
| W3D1 | [c03_control_fn](./crates/c03_control_fn/) | 迭代器、闭包 |
| W3D2 | [c05_threads](./crates/c05_threads/) | 多线程、通道、Mutex |

### 练习（按完成顺序）

| 阶段 | 练习 | 内容 |
|:---|:---|:---|
| W1D1 | [ex01_hello_move](./exercises/src/ownership_borrowing/) | 移动语义 |
| W1D2 | [ex02_move_clone](./exercises/src/ownership_borrowing/) | Clone vs Copy |
| W1D3 | [ex03_borrowing_rules](./exercises/src/ownership_borrowing/) | 借用规则 |
| W1D4 | [ex01_basic_types](./exercises/src/type_system/) | 基本类型 |
| W2D1 | [ex02_enum_match](./exercises/src/type_system/) | 枚举与模式匹配 |
| W2D2 | [ex01_basic_trait](./exercises/src/generics_traits/) | Trait 基础 |
| W2D3 | [ex01_result_option](./exercises/src/error_handling/) | Result 与 Option |
| W2D4 | [ex03_module_split](./exercises/src/type_system/) | 模块拆分 |
| W3D1 | [ex09_iterator_consumer](./exercises/rustlings_style/ex09_iterator_consumer/) | 迭代器消费 |
| W3D2 | [ex01_spawn_join](./exercises/src/concurrency/) | 线程 spawn/join |

---

## 学习效果自评

完成本路径后，你应该能够：

- [ ] 向同事解释 Rust 的所有权系统为什么能防止内存泄漏和数据竞争
- [ ] 独立编写包含错误处理、泛型和 trait 的 Rust 程序
- [ ] 使用 `cargo` 管理依赖、运行测试、生成文档
- [ ] 编写使用多线程和通道的并发程序，并保证线程安全
- [ ] 阅读 crates.io 上中等复杂度库的 API 文档并正确使用

如果以上任何一项尚未达标，建议返回对应阶段重新练习。

---

> **维护者**: 本项目知识库团队
> **最后更新**: 2026-05-31
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: 🧪 活跃维护中，欢迎反馈

---

## TRPL 3rd Edition 对照表

| TRPL 章节 | 本章主题 | 本项目对应文件 | 覆盖状态 | 差异说明 |
|:---|:---|:---|:---:|:---|
| Ch 1 | Getting Started | [concept/01_foundation/00_start.md](./concept/01_foundation/00_start.md) | ✅ | 安装、Cargo、Hello World 均覆盖 |
| Ch 2 | Programming a Guessing Game | [concept/01_foundation/07_control_flow.md](./concept/01_foundation/07_control_flow.md) | 🔄 | 控制流、随机数、循环有覆盖，但缺少完整猜数游戏项目 |
| Ch 3 | Common Programming Concepts | [concept/01_foundation/04_type_system.md](./concept/01_foundation/04_type_system.md) | ✅ | 变量、类型、函数、控制流全覆盖 |
| Ch 4 | Understanding Ownership | [concept/01_foundation/01_ownership.md](./concept/01_foundation/01_ownership.md) | ✅ | 所有权三规则、移动、Clone、Copy、Drop 全覆盖 |
| Ch 5 | Using Structs to Structure Related Data | [concept/01_foundation/04_type_system.md](./concept/01_foundation/04_type_system.md) | ✅ | struct、tuple struct、unit-like struct、方法语法均覆盖 |
| Ch 6 | Enums and Pattern Matching | [concept/01_foundation/04_type_system.md](./concept/01_foundation/04_type_system.md) | ✅ | enum、match、if let、Option 全覆盖 |
| Ch 7 | Managing Growing Projects with Packages, Crates, and Modules | [concept/02_intermediate/10_module_system.md](./concept/02_intermediate/10_module_system.md) | ✅ | package/crate/module/use/pub 全覆盖 |
| Ch 8 | Common Collections | [concept/01_foundation/08_collections.md](./concept/01_foundation/08_collections.md) | ✅ | Vec、String、HashMap 基础全覆盖 |
| Ch 9 | Error Handling with Result and Option | [concept/01_foundation/10_error_handling_basics.md](./concept/01_foundation/10_error_handling_basics.md) | ✅ | panic、Result、?、自定义错误全覆盖 |
| Ch 10 | Generic Types, Traits, and Lifetimes | [concept/02_intermediate/01_traits.md](./concept/02_intermediate/01_traits.md)<br>[concept/02_intermediate/02_generics.md](./concept/02_intermediate/02_generics.md)<br>[concept/01_foundation/03_lifetimes.md](./concept/01_foundation/03_lifetimes.md) | ✅ | 泛型、trait、生命周期基础全覆盖 |
| Ch 11 | Writing Automated Tests | [concept/01_foundation/16_testing_basics.md](./concept/01_foundation/16_testing_basics.md) | ✅ | 单元测试、集成测试、assert 宏全覆盖 |
| Ch 12 | An I/O Project: Building a Command Line Program | [LEARNING_MVP_PATH.md](./LEARNING_MVP_PATH.md)（Week 2 综合项目） | 🔄 | texttool/fastwc 项目覆盖 I/O 与 CLI，但非 TRPL 原文的 grep-like 项目 |
| Ch 13 | Functional Language Features: Iterators and Closures | [concept/01_foundation/15_closure_basics.md](./concept/01_foundation/15_closure_basics.md)<br>[concept/02_intermediate/15_iterator_patterns.md](./concept/02_intermediate/15_iterator_patterns.md) | ✅ | 闭包、迭代器、Iterator trait 全覆盖 |
| Ch 14 | More about Cargo and Crates.io | [concept/06_ecosystem/01_toolchain.md](./concept/06_ecosystem/01_toolchain.md)<br>[concept/06_ecosystem/62_cargo_registries_and_publishing.md](./concept/06_ecosystem/62_cargo_registries_and_publishing.md) | ✅ | Cargo 高级特性、发布、工作区均有覆盖 |
| Ch 15 | Smart Pointers | [concept/02_intermediate/12_smart_pointers.md](./concept/02_intermediate/12_smart_pointers.md) | ✅ | Box、Rc、RefCell、Arc 全覆盖 |
| Ch 16 | Fearless Concurrency | [concept/03_advanced/01_concurrency.md](./concept/03_advanced/01_concurrency.md) | ✅ | 线程、消息传递、共享状态、Send/Sync 全覆盖 |
| Ch 17 | Object-Oriented Programming Features of Rust | [concept/02_intermediate/19_advanced_traits.md](./concept/02_intermediate/19_advanced_traits.md) | 🔄 | trait 对象、封装、多态有覆盖，但 OOP 对比讨论较分散 |
| Ch 18 | Patterns and Matching | [concept/02_intermediate/05_assert_matches.md](./concept/02_intermediate/05_assert_matches.md) | 🔄 | match 模式已覆盖，但 destructuring、refutable/irrefutable 模式专题较少 |
| Ch 19 | Advanced Features | [concept/03_advanced/03_unsafe.md](./concept/03_advanced/03_unsafe.md)<br>[concept/02_intermediate/18_lifetimes_advanced.md](./concept/02_intermediate/18_lifetimes_advanced.md)<br>[concept/02_intermediate/20_type_system_advanced.md](./concept/02_intermediate/20_type_system_advanced.md) | ✅ | unsafe、高级 trait、高级生命周期、高级类型全覆盖 |
| Ch 20 | Final Project: Building a Multithreaded Web Server | [concept/03_advanced/18_network_programming.md](./concept/03_advanced/18_network_programming.md) | 🔄 | 网络编程与并发均有专题，但缺少 TRPL 原文的完整 web server 逐步项目 |
| Ch 21 | Appendix | [concept/00_meta/terminology_glossary.md](./concept/00_meta/terminology_glossary.md)<br>[concept/06_ecosystem/01_toolchain.md](./concept/06_ecosystem/01_toolchain.md) | 🔄 | 关键字、运算符、可派生 trait、工具链文档分散在各处，缺少统一附录索引 |

> **覆盖统计**：共 21 章，其中 ✅ 直接覆盖 17 章，🔄 部分覆盖 4 章，⬜ 未覆盖 0 章。
> **使用建议**：🔄 章节建议结合 TRPL 原文项目代码对照学习，以补齐项目式体验的差距。

---

## 扩展路径详细任务

> 以下任务为 `[选修]` 内容，完成 MVP 路径后根据个人兴趣选择。

### 方向 A：系统编程（+20h）

| 阶段 | 任务 | 内容 | 验证标准 |
|:---|:---|:---|:---|
| A1 | 阅读 Unsafe Rust | [03_unsafe.md](./concept/03_advanced/03_unsafe.md) 第 1–4 节 | 能解释 `unsafe` 块的 5 种能力 |
| A2 | 裸指针操作 | [crates/c01_ownership_borrow_scope](../../crates/c01_ownership_borrow_scope/) 运行 raw pointer 示例 | 全部编译通过 |
| A3 | FFI 调用 C 标准库 | [05_rust_ffi.md](./concept/03_advanced/05_rust_ffi.md) 第 1–3 节 | 成功调用 `libc::getpid()` 并打印 |
| A4 | 内联汇编初体验 | [13_inline_assembly.md](./concept/03_advanced/13_inline_assembly.md) 第 1–2 节 | 在 x86_64 上运行 `rdtsc` 示例 |
| A5 | 小项目 | 编写一个读取 `/proc/self/maps`（Linux）或系统信息（Windows）的 CLI 工具 | 使用 `unsafe` 调用平台 API，输出格式化 |

### 方向 B：Web 后端（+20h）

| 阶段 | 任务 | 内容 | 验证标准 |
|:---|:---|:---|:---|
| B1 | 阅读 Async/Await | [02_async.md](./concept/03_advanced/02_async.md) 第 1–4 节 | 能画出 Future 状态机转换图 |
| B2 | 运行 Tokio 示例 | [crates/c06_async](../../crates/c06_async/) 运行 hello_tokio | 成功运行异步 HTTP 客户端 |
| B3 | Axum 入门 | 使用 Axum 创建带路由的 Web 服务 | `curl http://localhost:3000/` 返回 JSON |
| B4 | 将 fastwc 改为 Web 服务 | 接受 HTTP POST 上传文件，返回统计结果 | 使用 `reqwest` 或 `curl` 测试通过 |

### 方向 C：形式化验证（+40h）

| 阶段 | 任务 | 内容 | 验证标准 |
|:---|:---|:---|:---|
| C1 | 阅读 RustBelt 直觉 | [04_rustbelt.md](./concept/04_formal/04_rustbelt.md) 第 1–3 节 | 能解释分离逻辑的基本思想 |
| C2 | Kani 安装与运行 | [22_modern_verification_tools.md](./concept/04_formal/22_modern_verification_tools.md) 快速开始 | `cargo kani --harness` 成功验证一个函数 |
| C3 | 验证 Vec::push | 为 `Vec::push` 编写 Kani harness，验证无越界 | Kani 报告 "successful" |
| C4 | Miri 运行 | `cargo miri test` 运行 c01_ownership_borrow_scope 测试 | 无 UB 报告 |

---
