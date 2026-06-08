# Rust 最小可行学习路径（MVP Path）

> **目标受众**: [初学者]
> **预计耗时**: 35–45 小时（按每天 2 小时，约 3 周完成）
> **路径终点**: 独立编写一个多线程命令行工具（CLI）
> **设计原则**: 每个阶段必须有可运行的代码，每个概念必须有对应的练习验证

---

## 📑 路径概览

```text
Week 1: Rust 基础与所有权系统（12h）
    ├─ 第 1 天：Hello World + 工具链（2h）
    ├─ 第 2 天：所有权与移动语义（2h）
    ├─ 第 3 天：借用与引用（2h）
    ├─ 第 4 天：基本类型与集合（2h）
    └─ 第 5–6 天：综合练习 + Checkpoint（4h）

Week 2: 类型系统与错误处理（12h）
    ├─ 第 7 天：结构体、枚举与模式匹配（2h）
    ├─ 第 8 天：Trait 与泛型入门（2h）
    ├─ 第 9 天：错误处理（2h）
    ├─ 第 10 天：模块与 Cargo（2h）
    └─ 第 11–12 天：综合练习 + Checkpoint（4h）

Week 3: 并发与 CLI 项目（12h）
    ├─ 第 13 天：迭代器与闭包（2h）
    ├─ 第 14 天：多线程基础（2h）
    ├─ 第 15–16 天：CLI 项目实战（4h）
    ├─ 第 17 天：代码审查与优化（2h）
    └─ 第 18 天：最终 Checkpoint + 扩展路径（2h）
```

> **为什么要学所有权？** 所有权是 Rust 最独特、最核心的概念，也是后续所有安全保证的基础。
> Week 1 的投入将在 Week 3 的并发编程中获得十倍回报——无需担心数据竞争。

---

## Week 1：Rust 基础与所有权系统（12h）

### 第 1 天：Hello World + 工具链（2h）

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

### 第 2 天：所有权与移动语义（2h）

**学习目标**：深入理解所有权三规则、Drop 语义、`Clone` 与 `Copy`。

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/01_foundation/01_ownership.md](./concept/01_foundation/01_ownership.md) 第 4–7 节 | 40min | — |
| 代码 | [crates/c01_ownership_borrow_scope](./crates/c01_ownership_borrow_scope/) 运行 ownership 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/src/ownership_borrowing/ex02_move_clone.rs](./exercises/src/ownership_borrowing/) | 30min | 测试通过 |
| 测验 | 完成 [01_ownership.md 嵌入式测验 1–3](./concept/01_foundation/01_ownership.md#嵌入式测验) | 20min | 全部答对 |

---

### 第 3 天：借用与引用（2h）

**学习目标**：掌握不可变借用 `&T`、可变借用 `&mut T`、借用规则。

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/01_foundation/02_borrowing.md](./concept/01_foundation/02_borrowing.md) | 45min | — |
| 代码 | [crates/c01_ownership_borrow_scope](./crates/c01_ownership_borrow_scope/) 运行 borrowing 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/src/ownership_borrowing/ex03_borrowing_rules.rs](./exercises/src/ownership_borrowing/) | 30min | 测试通过 |
| 测验 | 完成 [02_borrowing.md 嵌入式测验 1–3](./concept/01_foundation/02_borrowing.md#嵌入式测验) | 15min | 全部答对 |

---

### 第 4 天：基本类型与集合（2h）

**学习目标**：理解 Rust 的类型系统基础，掌握 Vec、HashMap 的基本用法。

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/01_foundation/04_type_system.md](./concept/01_foundation/04_type_system.md) 第 1–4 节 | 35min | — |
| 阅读 | [concept/01_foundation/08_collections.md](./concept/01_foundation/08_collections.md) 第 1–3 节 | 25min | — |
| 代码 | [crates/c02_type_system](./crates/c02_type_system/) 运行 collections 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/src/type_system/ex01_basic_types.rs](./exercises/src/type_system/) | 30min | 测试通过 |

---

### 第 5–6 天：Week 1 综合练习 + Checkpoint（4h）

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

### 第 7 天：结构体、枚举与模式匹配（2h）

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/01_foundation/04_type_system.md](./concept/01_foundation/04_type_system.md) 第 5–7 节（struct/enum/match） | 40min | — |
| 代码 | [crates/c02_type_system](./crates/c02_type_system/) 运行 enum_pattern 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/src/type_system/ex02_enum_match.rs](./exercises/src/type_system/) | 30min | 测试通过 |
| 小项目 | 为 `wordcount` 添加 `--lines-only`、`--words-only` 选项（使用 enum） | 20min | 功能正确 |

---

### 第 8 天：Trait 与泛型入门（2h）

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/02_intermediate/01_traits.md](./concept/02_intermediate/01_traits.md) 第 1–4 节 | 35min | — |
| 阅读 | [concept/02_intermediate/02_generics.md](./concept/02_intermediate/02_generics.md) 第 1–3 节 | 25min | — |
| 代码 | [crates/c04_generic](./crates/c04_generic/) 运行 trait_basics 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/src/generics_traits/ex01_basic_trait.rs](./exercises/src/generics_traits/) | 30min | 测试通过 |

---

### 第 9 天：错误处理（2h）

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/01_foundation/10_error_handling_basics.md](./concept/01_foundation/10_error_handling_basics.md) | 40min | — |
| 代码 | [crates/c03_control_fn](./crates/c03_control_fn/) 运行 error_handling 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/src/error_handling/ex01_result_option.rs](./exercises/src/error_handling/) | 30min | 测试通过 |
| 重构 | 将 `wordcount` 的 `expect` 改为 `Result` 传播（使用 `?`） | 20min | 功能正确，无 panic |

---

### 第 10 天：模块与 Cargo（2h）

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/02_intermediate/10_module_system.md](./concept/02_intermediate/10_module_system.md) 第 1–3 节 | 30min | — |
| 代码 | 将 `wordcount` 拆分为 `lib.rs`（逻辑）和 `main.rs`（CLI） | 40min | `cargo test` 通过 |
| 练习 | [exercises/src/type_system/ex03_module_split.rs](./exercises/src/type_system/) | 30min | 测试通过 |
| 阅读 | [Cargo 工作区指南](./docs/03_guides/) | 20min | 理解 workspace 概念 |

---

### 第 11–12 天：Week 2 综合练习 + Checkpoint（4h）

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

### 第 13 天：迭代器与闭包（2h）

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/01_foundation/15_closure_basics.md](./concept/01_foundation/15_closure_basics.md) | 30min | — |
| 阅读 | [concept/02_intermediate/15_iterator_patterns.md](./concept/02_intermediate/15_iterator_patterns.md) 第 1–3 节 | 30min | — |
| 代码 | [crates/c03_control_fn](./crates/c03_control_fn/) 运行 iterator_closure 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/rustlings_style/ex09_iterator_consumer](./exercises/rustlings_style/ex09_iterator_consumer/) | 30min | 测试通过 |

---

### 第 14 天：多线程基础（2h）

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 阅读 | [concept/03_advanced/01_concurrency.md](./concept/03_advanced/01_concurrency.md) 第 1–4 节 | 40min | — |
| 代码 | [crates/c05_threads](./crates/c05_threads/) 运行 spawn_join 示例 | 30min | 全部示例编译通过 |
| 练习 | [exercises/src/concurrency/ex01_spawn_join.rs](./exercises/src/concurrency/) | 30min | 测试通过 |
| 关键理解 | 为什么 `move` 闭包在线程中必要？ | 20min | 能用自己的话解释 |

---

### 第 15–16 天：多线程 CLI 项目实战（4h）

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

### 第 17 天：代码审查与优化（2h）

| 任务 | 内容 | 预计时间 | 验证标准 |
|:---|:---|:---:|:---|
| 审查 | 使用 `cargo clippy` 检查 `fastwc` | 15min | 0 warning |
| 优化 | 使用 `BufReader` 替代逐行 `read_to_string` | 30min | 性能提升可见 |
| 文档 | 为 `lib.rs` 添加 doc comments | 30min | `cargo doc` 生成清晰文档 |
| 测试 | 使用 `tempfile` crate 编写集成测试 | 45min | 测试覆盖主要路径 |

---

### 第 18 天：最终 Checkpoint + 扩展路径（2h）

**最终 Checkpoint**（项目级评估）：

1. 向同伴（或录音）解释：`fastwc` 为什么不会有数据竞争？
2. 如果要在 `fastwc` 中使用 `crossbeam::channel` 替代 `mpsc`，需要改哪些代码？
3. 画出 `fastwc` 的线程 + 通道数据流图。

**扩展路径选择**（根据兴趣选一个方向）：

| 方向 | 下一步 | 预计时间 |
|:---|:---|:---:|
| **系统编程** | 学习 Unsafe + FFI，尝试调用 C 库 | +20h |
| **Web 后端** | 学习 Axum/Tokio，将 `fastwc` 改为 Web 服务 | +20h |
| **嵌入式** | 学习 `no_std`，在 microcontroller 上运行 Rust | +30h |
| **形式化验证** | 进入 [L4 形式化](./concept/04_formal/README.md)，理解所有权证明 | +40h |
| **开源贡献** | 为 [rust-lang/rust](https://github.com/rust-lang/rust) 或 [tokio](https://github.com/tokio-rs/tokio) 提交文档 PR | 持续 |

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
