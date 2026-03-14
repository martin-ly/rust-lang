# 本项目概念与官方资源映射表

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 本项目概念/模块 ↔ The Rust Book / Reference / Rust by Example

---

## 官方资源入口

| 资源 | URL | 说明 |
| :--- | :--- | :--- |
| **The Rust Book** | <https://doc.rust-lang.org/book/> | 官方入门教程，Ch 1-22 |
| **Rust Reference** | <https://doc.rust-lang.org/reference/> | 语言规范 |
| **Rust by Example** | <https://doc.rust-lang.org/rust-by-example/> | 示例驱动学习，24个主题 |
| **Standard Library** | <https://doc.rust-lang.org/std/> | 标准库 API |
| **Rust releases** | <https://releases.rs/> | 版本 changelog |
| **Brown 交互版 Book** | <https://rust-book.cs.brown.edu/> | 测验、可视化、高亮（Rust Book 交互版） |
| **Rustlings** | <https://github.com/rust-lang/rustlings> | 命令行交互式习题 |
| **Compiler Error Index** | <https://doc.rust-lang.org/error-index.html> | 编译器错误详解 |
| **Command Line Book** | <https://rust-cli.github.io/book/> | CLI 应用开发 |
| **Embedded Rust Book** | <https://doc.rust-lang.org/embedded-book/> | 嵌入式开发 |

---

## 模块 → 官方章节映射

| 项目模块 | 本项目路径 | The Rust Book | RBE 练习（可点击） | Reference |
| :--- | :--- | :--- | :--- | :--- |
| **C02 类型系统** | crates/c02_type_system | Ch 3 Types, Ch 10 Traits | [Custom Types](https://doc.rust-lang.org/rust-by-example/custom_types.html) · [Traits](https://doc.rust-lang.org/rust-by-example/trait.html) · [Conversion](https://doc.rust-lang.org/rust-by-example/conversion.html) | [Types](https://doc.rust-lang.org/reference/types.html) |
| **C03 控制流** | crates/c03_control_fn | Ch 3 Control Flow, Ch 6 Enums | [Flow Control](https://doc.rust-lang.org/rust-by-example/flow_control.html) · [Option](https://doc.rust-lang.org/rust-by-example/std/option.html) · [Error](https://doc.rust-lang.org/rust-by-example/error.html) · [Iterator](https://doc.rust-lang.org/rust-by-example/trait/iter.html) | [Statements](https://doc.rust-lang.org/reference/statements.html) |
| **C04 泛型** | crates/c04_generic | Ch 10 Generic Types, Traits | [Generics](https://doc.rust-lang.org/rust-by-example/generics.html) | [Items](https://doc.rust-lang.org/reference/items/generics.html) |
| **C05 线程** | crates/c05_threads | Ch 16 Fearless Concurrency | [Threads](https://doc.rust-lang.org/rust-by-example/std_misc/threads.html) | [Send/Sync](https://doc.rust-lang.org/reference/special-types-and-traits.html) |
| **C06 异步** | crates/c06_async | Ch 17 Async | [Async](https://doc.rust-lang.org/rust-by-example/async.html) | [Coroutines](https://doc.rust-lang.org/reference/items/coroutines.html) |
| **C07 进程** | crates/c07_process | - | [Process](https://doc.rust-lang.org/rust-by-example/std_misc/process.html) | [Process](https://doc.rust-lang.org/std/process/) |
| **C08 算法** | crates/c08_algorithms | - | [Vectors](https://doc.rust-lang.org/rust-by-example/std/vec.html) · [HashMap](https://doc.rust-lang.org/rust-by-example/std/hash.html) · [Iterator](https://doc.rust-lang.org/rust-by-example/trait/iter.html) | [Iterator](https://doc.rust-lang.org/std/iter/) |
| **C09 设计模式** | crates/c09_design_pattern | Ch 18 OOP | [Functional](https://doc.rust-lang.org/rust-by-example/fn.html) · [Structs](https://doc.rust-lang.org/rust-by-example/custom_types/structs.html) · [Enums](https://doc.rust-lang.org/rust-by-example/custom_types/enum.html) | - |
| **C10 网络** | crates/c10_networks | - | [TCP](https://doc.rust-lang.org/rust-by-example/std_misc/net.html) | [net](https://doc.rust-lang.org/std/net/) |
| **C11 宏** | crates/c11_macro_system | Ch 20.5 Macros | [Macros](https://doc.rust-lang.org/rust-by-example/macros.html) | [Macros](https://doc.rust-lang.org/reference/macros.html) |
| **C12 WASM** | crates/c12_wasm | - | - | [wasm-bindgen](https://rustwasm.github.io/wasm-bindgen/) |

---

## 小节级精确映射

### The Rust Book Ch 1-22 详细映射

#### 第1章：Getting Started

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 1.1 Installation | 安装 Rust、rustup、验证安装 | [LEARNING_PATH_PLANNING.md](./LEARNING_PATH_PLANNING.md) § 环境准备 | 补充多版本管理、IDE配置 |
| 1.2 Hello, World! | 第一个程序、编译运行 | `crates/c01_basic/` 基础示例 | 补充 rustc 选项详解 |
| 1.3 Hello, Cargo! | Cargo 基础、构建运行 | [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) | 补充 Cargo.toml 全字段参考 |

#### 第2章：Programming a Guessing Game

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 完整章节 | 猜数字游戏完整实现 | `examples/guessing_game/` 示例 | 代码解析 + 扩展练习 |

#### 第3章：Common Programming Concepts

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 3.1 Variables and Mutability | 变量、可变性、常量、遮蔽 | [ownership_cheatsheet](../02_reference/quick_reference/ownership_cheatsheet.md) § 基础 | 变量作用域深入分析 |
| 3.2 Data Types | 标量类型、复合类型 | [type_system](../02_reference/quick_reference/type_system.md) § 基础类型 | 类型推断算法说明 |
| 3.3 Functions | 函数定义、参数、返回值 | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md) | 函数签名设计模式 |
| 3.4 Comments | 注释语法 | - | 官方充分覆盖 |
| 3.5 Control Flow | if、loop、while、for | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md) § 控制流 | 控制流决策树 |

#### 第4章：Understanding Ownership

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 4.1 What is Ownership? | 所有权规则、内存安全 | [ownership_model](../research_notes/formal_methods/ownership_model.md) | 形式化所有权证明 |
| 4.2 References and Borrowing | 引用、借用规则 | [borrow_checker_proof](../research_notes/formal_methods/borrow_checker_proof.md) | 借用检查器内部机制 |
| 4.3 The Slice Type | 切片、字符串 slice | `crates/c02_type_system/src/slice_examples.rs` | 切片边界检查分析 |

#### 第5章：Using Structs

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 5.1 Defining and Instantiating Structs | 结构体定义、实例化 | [type_system](../02_reference/quick_reference/type_system.md) § Struct | 结构体内存布局 |
| 5.2 An Example Program Using Structs | 示例程序 | `examples/struct_demo/` | 扩展示例 |
| 5.3 Methods | 方法定义、关联函数 | [type_system](../02_reference/quick_reference/type_system.md) § Methods | 方法解析规则 |

#### 第6章：Enums and Pattern Matching

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 6.1 Defining an Enum | 枚举定义、Option、Result | [type_system](../02_reference/quick_reference/type_system.md) § Enum | 代数数据类型理论 |
| 6.2 The match Control Flow Construct | match 语法 | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md) § match | 穷尽性检查算法 |
| 6.3 Concise Control Flow with if let and let else | if let、let-else | `crates/c03_control_fn/src/` | 模式匹配决策树 |

#### 第7章：Packages, Crates, and Modules

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 7.1 Packages and Crates | Package、Crate 概念 | [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) § 工作区 | crate 类型详解 |
| 7.2 Control Scope and Privacy with Modules | 模块、可见性 | `crates/c10_networks/src/lib.rs` 示例 | 模块系统最佳实践 |
| 7.3 Paths for Referring to an Item in the Module Tree | 路径语法 | [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) | 路径解析规则 |
| 7.4 Bringing Paths Into Scope with the use Keyword | use 声明 | `crates/` 各 crate 示例 | use 合并技巧 |
| 7.5 Separating Modules into Different Files | 文件组织 | 本项目 crates/ 目录结构 | 项目结构模板 |

#### 第8章：Common Collections

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 8.1 Storing Lists of Values with Vectors | Vec | [collections_iterators_cheatsheet](../02_reference/quick_reference/collections_iterators_cheatsheet.md) § Vec | Vec 内存布局 |
| 8.2 Storing UTF-8 Encoded Text with Strings | String、&str | [collections_iterators_cheatsheet](../02_reference/quick_reference/collections_iterators_cheatsheet.md) § String | 字符串编码深入 |
| 8.3 Storing Keys with Associated Values in Hash Maps | HashMap | [collections_iterators_cheatsheet](../02_reference/quick_reference/collections_iterators_cheatsheet.md) § HashMap | 哈希算法比较 |

#### 第9章：Error Handling

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 9.1 Unrecoverable Errors with panic! | panic!、unwind | [error_handling_cheatsheet](../02_reference/quick_reference/error_handling_cheatsheet.md) § panic | panic hook 自定义 |
| 9.2 Recoverable Errors with Result | Result、? 运算符 | [error_handling_cheatsheet](../02_reference/quick_reference/error_handling_cheatsheet.md) § Result | 错误传播转换树 |
| 9.3 To panic! or Not to panic! | panic vs Result 决策 | [THINKING_REPRESENTATION_METHODS](../04_thinking/THINKING_REPRESENTATION_METHODS.md) | 错误处理决策流程 |

#### 第10章：Generic Types, Traits, and Lifetimes

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 10.1 Generic Data Types | 泛型函数、结构体 | [generics_cheatsheet](../02_reference/quick_reference/generics_cheatsheet.md) | 单态化机制 |
| 10.2 Defining Shared Behavior with Traits | Trait 定义、实现 | [type_system](../02_reference/quick_reference/type_system.md) § Traits | Trait 对象 vs 泛型 |
| 10.3 Validating References with Lifetimes | 生命周期语法 | [variance_theory](../research_notes/type_theory/variance_theory.md) | 型变理论、形式化证明 |

#### 第11章：Writing Automated Tests

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 11.1 How to Write Tests | 测试函数、assert | [testing_cheatsheet](../02_reference/quick_reference/testing_cheatsheet.md) § 单元测试 | 测试覆盖率工具 |
| 11.2 Controlling How Tests Are Run | 测试过滤、并行 | [testing_cheatsheet](../02_reference/quick_reference/testing_cheatsheet.md) § cargo test 选项 | nextest 工具链 |
| 11.3 Test Organization | 单元/集成测试 | [testing_cheatsheet](../02_reference/quick_reference/testing_cheatsheet.md) § 测试组织 | 测试架构模式 |

#### 第12章：An I/O Project

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 12.1 Accepting Command Line Arguments | 命令行参数 | [CLI_APPLICATIONS_GUIDE](../05_guides/CLI_APPLICATIONS_GUIDE.md) § 参数解析 | clap 库详解 |
| 12.2 Reading a File | 文件读取 | `crates/c07_process/src/file_ops.rs` | 异步文件 I/O |
| 12.3 Refactoring to Improve Modularity and Error Handling | 重构、错误处理 | [CLI_APPLICATIONS_GUIDE](../05_guides/CLI_APPLICATIONS_GUIDE.md) | 项目架构模式 |
| 12.4 Adding Functionality with Test Driven Development | TDD | [testing_cheatsheet](../02_reference/quick_reference/testing_cheatsheet.md) § TDD | 属性测试 |
| 12.5 Working with Environment Variables | 环境变量 | `crates/c07_process/src/env.rs` | 配置管理 |
| 12.6 Redirecting Errors to Standard Error | 标准错误 | [CLI_APPLICATIONS_GUIDE](../05_guides/CLI_APPLICATIONS_GUIDE.md) § 日志 | tracing 集成 |

#### 第13章：Functional Language Features

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 13.1 Closures | 闭包、捕获环境 | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md) | 闭包内存布局 |
| 13.2 Processing a Series of Items with Iterators | Iterator | [collections_iterators_cheatsheet](../02_reference/quick_reference/collections_iterators_cheatsheet.md) § Iterator | 自定义迭代器 |
| 13.3 Improving Our I/O Project | 应用改进 | `examples/` 各示例 | 最佳实践 |
| 13.4 Performance in Loops vs. Iterators | 性能比较 | [collections_iterators_cheatsheet](../02_reference/quick_reference/collections_iterators_cheatsheet.md) § 性能 | 零成本抽象证明 |

#### 第14章：More about Cargo and Crates.io

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 14.1 Customizing Builds with Release Profiles | Release Profiles | [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) § Profile | 优化选项详解 |
| 14.2 Publishing a Crate to Crates.io | 发布流程 | [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) § 发布 | semver 规范 |
| 14.3 Cargo Workspaces | 工作区 | `Cargo.workspace` 本项目配置 | 大型项目管理 |
| 14.4 Installing Binaries with cargo install | cargo install | [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) | binstall 工具 |
| 14.5 Extending Cargo with Custom Commands | 自定义命令 | [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) § 扩展 | cargo-make 等 |

#### 第15章：Smart Pointers

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 15.1 Using `Box<T>` to Point to Data on the Heap | Box | [smart_pointers_cheatsheet](../02_reference/quick_reference/smart_pointers_cheatsheet.md) § Box | 堆分配策略 |
| 15.2 Treating Smart Pointers Like Regular References | Deref | [smart_pointers_cheatsheet](../02_reference/quick_reference/smart_pointers_cheatsheet.md) § Deref | 自动解引用规则 |
| 15.3 Running Code on Cleanup with the Drop Trait | Drop | [smart_pointers_cheatsheet](../02_reference/quick_reference/smart_pointers_cheatsheet.md) § Drop | RAII 模式 |
| 15.4 `Rc<T>`, the Reference Counted Smart Pointer | Rc | [smart_pointers_cheatsheet](../02_reference/quick_reference/smart_pointers_cheatsheet.md) § Rc | 循环引用检测 |
| 15.5 `RefCell<T>` and the Interior Mutability Pattern | RefCell | [smart_pointers_cheatsheet](../02_reference/quick_reference/smart_pointers_cheatsheet.md) § RefCell | 运行时借用检查 |
| 15.6 Reference Cycles Can Leak Memory | 循环引用 | [smart_pointers_cheatsheet](../02_reference/quick_reference/smart_pointers_cheatsheet.md) § Weak | 内存泄漏分析 |

#### 第16章：Fearless Concurrency

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 16.1 Using Threads to Run Code Simultaneously | 线程创建、join | [threads_concurrency_cheatsheet](../02_reference/quick_reference/threads_concurrency_cheatsheet.md) § 线程 | 线程池实现 |
| 16.2 Transfer Data Between Threads with Message Passing | Channel | [threads_concurrency_cheatsheet](../02_reference/quick_reference/threads_concurrency_cheatsheet.md) § Channel | async-channel |
| 16.3 Shared-State Concurrency | Mutex、Arc | [threads_concurrency_cheatsheet](../02_reference/quick_reference/threads_concurrency_cheatsheet.md) § 同步原语 | 锁粒度优化 |
| 16.4 Extensible Concurrency with Send and Sync | Send、Sync | [send_sync_formalization](../research_notes/formal_methods/send_sync_formalization.md) | 形式化证明 |

#### 第17章：Asynchronous Programming

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 17.1 Futures and the Async Syntax | async/await | [async_patterns](../02_reference/quick_reference/async_patterns.md) § 基础 | 状态机转换 |
| 17.2 Applying Concurrency with Async | 并发执行 | [async_patterns](../02_reference/quick_reference/async_patterns.md) § 并发 | join!/select! |
| 17.3 Working With Any Number of Futures | 动态 Future | [async_patterns](../02_reference/quick_reference/async_patterns.md) § Stream | FuturesUnordered |
| 17.4 Streams: Futures in Sequence | Stream | [async_patterns](../02_reference/quick_reference/async_patterns.md) § Stream | 背压处理 |
| 17.5 A Closer Look at the Traits for Async | Async Traits | [async_patterns](../02_reference/quick_reference/async_patterns.md) § Traits | RPITIT 详解 |
| 17.6 Futures, Tasks, and Threads | 运行时对比 | [async_state_machine](../research_notes/formal_methods/async_state_machine.md) | 调度器原理 |

#### 第18章：Object Oriented Programming Features

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 18.1 Characteristics of Object-Oriented Languages | OOP 特性对比 | [design_patterns](../../crates/c09_design_pattern/docs/README.md) § OOP | 设计模式映射 |
| 18.2 Using Trait Objects to Abstract over Shared Behavior | Trait Objects | [type_system](../02_reference/quick_reference/type_system.md) § 动态分发 | vtable 布局 |
| 18.3 Implementing an Object-Oriented Design Pattern | 状态模式 | `crates/c09_design_pattern/src/state_pattern.rs` | 其他模式实现 |

#### 第19章：Patterns and Matching

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 19.1 All the Places Patterns Can Be Used | 模式使用位置 | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md) § 模式 | 模式匹配决策树 |
| 19.2 Refutability: Whether a Pattern Might Fail to Match | 可反驳性 | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md) § 模式 | 穷尽性检查 |
| 19.3 Pattern Syntax | 模式语法大全 | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md) § 模式 | 高级模式技巧 |

#### 第20章：Advanced Features

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 20.1 Unsafe Rust | unsafe 代码 | [UNSAFE_RUST_GUIDE](../05_guides/UNSAFE_RUST_GUIDE.md) | 完整 unsafe 指南 |
| 20.2 Advanced Traits | 关联类型、完全限定语法 | [type_system](../02_reference/quick_reference/type_system.md) § 高级 | 复杂 trait 模式 |
| 20.3 Advanced Types | 类型别名、never type | [type_system](../02_reference/quick_reference/type_system.md) § 高级 | 类型级编程 |
| 20.4 Advanced Functions and Closures | 函数指针、返回闭包 | [closures_cheatsheet](../02_reference/quick_reference/closures_cheatsheet.md) § 高级 | HRTB |
| 20.5 Macros | 声明宏、过程宏 | [macros_cheatsheet](../02_reference/quick_reference/macros_cheatsheet.md) | 宏编写指南 |

#### 第21章：Final Project

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 21.1-21.3 Web Server | 多线程 Web 服务器 | `examples/web_server/` | 完整实现 + 优化 |

#### 第22章：Appendix

| 小节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| 22.1 Keywords | 关键字列表 | [QUICK_REFERENCE](../research_notes/QUICK_REFERENCE.md) | 快速参考 |
| 22.2 Operators and Symbols | 运算符 | [QUICK_REFERENCE](../research_notes/QUICK_REFERENCE.md) | 运算符优先级 |
| 22.3 Derivable Traits | 可派生 Trait | [type_system](../02_reference/quick_reference/type_system.md) § Derive | 自定义 derive |
| 22.4 Useful Development Tools | 开发工具 | [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) § 工具 | 完整工具链 |
| 22.5 Editions | Edition 差异 | [09_rust_1.93_compatibility_deep_dive](../06_toolchain/09_rust_1.93_compatibility_deep_dive.md) | 迁移指南 |
| 22.6-22.7 | 翻译、开发流程 | - | 官方充分覆盖 |

---

### Rust Reference 主要章节映射

| 章节 | 官方内容 | 本项目映射 | 补充说明 |
|------|---------|-----------|---------|
| **2. Lexical Structure** | 词法结构 | [QUICK_REFERENCE](../research_notes/QUICK_REFERENCE.md) § 语法 | 快速参考 |
| **3. Macros** | 宏系统 | [macros_cheatsheet](../02_reference/quick_reference/macros_cheatsheet.md) | 宏决策树 |
| **6. Items** | 所有 Item 类型 | 各 crate 源码示例 | 实战示例 |
| **8. Statements and Expressions** | 语句与表达式 | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md) | 控制流决策树 |
| **9. Patterns** | 模式 | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md) § 模式 | 穷尽性分析 |
| **10. Type System** | 类型系统 | [type_system](../02_reference/quick_reference/type_system.md) | 型变理论 |
| **10.5 Subtyping and Variance** | 子类型与型变 | [variance_theory](../research_notes/type_theory/variance_theory.md) | 形式化证明 |
| **11. Special Types and Traits** | 特殊类型和 Trait | [send_sync_formalization](../research_notes/formal_methods/send_sync_formalization.md) | Send/Sync 形式化 |
| **13. Memory Model** | 内存模型 | [ownership_model](../research_notes/formal_methods/ownership_model.md) | 所有权证明 |
| **17. Unsafety** | Unsafe | [UNSAFE_RUST_GUIDE](../05_guides/UNSAFE_RUST_GUIDE.md) | UB 完整列表 |

---

### Rust by Example 24 主题映射

| # | 主题 | 官方内容 | 本项目映射 |
|---|------|---------|-----------|
| 1 | **Hello World** | 基础打印、注释 | `crates/c01_basic/` |
| 2 | **Primitives** | 基本类型、元组、数组 | [type_system](../02_reference/quick_reference/type_system.md) |
| 3 | **Custom Types** | struct、enum | [type_system](../02_reference/quick_reference/type_system.md) § 自定义类型 |
| 4 | **Variable Bindings** | 可变性、作用域 | [ownership_cheatsheet](../02_reference/quick_reference/ownership_cheatsheet.md) |
| 5 | **Types** | 类型转换、推断 | [type_system](../02_reference/quick_reference/type_system.md) |
| 6 | **Conversion** | From/Into、TryFrom | [type_system](../02_reference/quick_reference/type_system.md) § 转换 |
| 7 | **Expressions** | 表达式语法 | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md) |
| 8 | **Flow of Control** | if/else、loop、match | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md) |
| 9 | **Functions** | 函数、闭包、高阶函数 | [closures_cheatsheet](../02_reference/quick_reference/closures_cheatsheet.md) |
| 10 | **Modules** | 模块系统 | `crates/` 项目结构 |
| 11 | **Crates** | 库创建 | [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) |
| 12 | **Cargo** | 包管理 | [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) |
| 13 | **Attributes** | 属性 | [macros_cheatsheet](../02_reference/quick_reference/macros_cheatsheet.md) |
| 14 | **Generics** | 泛型 | [generics_cheatsheet](../02_reference/quick_reference/generics_cheatsheet.md) |
| 15 | **Scoping Rules** | 所有权、借用、生命周期 | [ownership_model](../research_notes/formal_methods/ownership_model.md) |
| 16 | **Traits** | Trait 系统 | [type_system](../02_reference/quick_reference/type_system.md) § Traits |
| 17 | **macro_rules!** | 声明宏 | [macros_cheatsheet](../02_reference/quick_reference/macros_cheatsheet.md) |
| 18 | **Error Handling** | 错误处理 | [error_handling_cheatsheet](../02_reference/quick_reference/error_handling_cheatsheet.md) |
| 19 | **Std Library Types** | 标准库类型 | [collections_iterators_cheatsheet](../02_reference/quick_reference/collections_iterators_cheatsheet.md) |
| 20 | **Std Misc** | 线程、文件、进程 | [threads_concurrency_cheatsheet](../02_reference/quick_reference/threads_concurrency_cheatsheet.md) |
| 21 | **Testing** | 测试 | [testing_cheatsheet](../02_reference/quick_reference/testing_cheatsheet.md) |
| 22 | **Unsafe Operations** | Unsafe 操作 | [UNSAFE_RUST_GUIDE](../05_guides/UNSAFE_RUST_GUIDE.md) |
| 23 | **Compatibility** | 兼容性 | [09_rust_1.93_compatibility_deep_dive](../06_toolchain/09_rust_1.93_compatibility_deep_dive.md) |
| 24 | **Meta** | 文档、Playground | [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) |

---

## 差距分析

### 官方覆盖但本项目缺失的内容

| 官方资源 | 缺失内容 | 优先级 | 计划补充 |
|---------|---------|--------|---------|
| **Book Ch 21** | Web Server 完整实现 | 中 | `examples/web_server/` |
| **Reference Ch 19-20** | ABI、运行时细节 | 低 | 链接到官方文档 |
| **Embedded Book** | 嵌入式开发 | 低 | 暂不提供，使用官方 |
| **WebAssembly Book** | WASM 深入 | 中 | [wasm_cheatsheet](../02_reference/quick_reference/wasm_cheatsheet.md) |
| **Rustonomicon** | Unsafe 高级模式 | 中 | [UNSAFE_RUST_GUIDE](../05_guides/UNSAFE_RUST_GUIDE.md) |

### 本项目补充的官方未覆盖内容

| 补充内容 | 位置 | 说明 |
|---------|------|------|
| **型变理论形式化** | [variance_theory](../research_notes/type_theory/variance_theory.md) | 官方仅提及概念，无理论深度 |
| **Send/Sync 形式化证明** | [send_sync_formalization](../research_notes/formal_methods/send_sync_formalization.md) | 官方仅定义 trait，无证明 |
| **借用检查器内部机制** | [borrow_checker_proof](../research_notes/formal_methods/borrow_checker_proof.md) | 官方无实现细节 |
| **异步状态机形式化** | [async_state_machine](../research_notes/formal_methods/async_state_machine.md) | 官方无形式化模型 |
| **宏系统决策树** | [macros_cheatsheet](../02_reference/quick_reference/macros_cheatsheet.md) | 官方为参考文档 |
| **错误传播转换树** | [THINKING_REPRESENTATION_METHODS](../04_thinking/THINKING_REPRESENTATION_METHODS.md) | 官方为教程式讲解 |
| **版本兼容性深度分析** | [09_rust_1.93_compatibility_deep_dive](../06_toolchain/09_rust_1.93_compatibility_deep_dive.md) | 官方仅列变更 |
| **控制流决策树** | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md) | 官方分散在各章 |
| **异步模式反例** | [async_patterns](../02_reference/quick_reference/async_patterns.md) | 官方无反模式说明 |
| **所有权模型可视化** | [ownership_model](../research_notes/formal_methods/ownership_model.md) | 官方无形式化描述 |

### 版本差异说明

| 特性 | 官方版本 | 本项目版本 | 差异说明 |
|------|---------|-----------|---------|
| **Rust Edition** | 2024 (1.85.0+) | 2024 (1.94.0+) | 本项目跟踪最新版 |
| **async closure** | 1.85 新增 | 完整覆盖 | 补充形式化分析 |
| `offset_of!` | 1.93 类型检查增强 | 已更新 | 详见兼容性分析 |
| `#[test]` 严格化 | 1.93 新要求 | 已更新 | 详见兼容性分析 |
| `gen` 关键字 | 1.93 nightly | 跟踪中 | 生成器语法 |
| **trait 系统** | 基础 | RPITIT、AFIT 详解 | 补充高级用法 |

---

## 学习路径优化

### 路径一：新手入门路径（零基础 → 能写简单项目）

**预计时间**: 4-6 周

| 阶段 | 官方资源 | 本项目补充 | 练习 |
|------|---------|-----------|------|
| **Week 1: 环境 + 基础语法** | Book Ch 1-3 | [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) | [Rustlings](https://github.com/rust-lang/rustlings) intro |
| **Week 2: 所有权系统** | Book Ch 4 + RBE Scoping Rules | [ownership_cheatsheet](../02_reference/quick_reference/ownership_cheatsheet.md) | RBE 15.1-15.4 |
| **Week 3: 复合类型 + 集合** | Book Ch 5-8 + RBE Custom Types | [type_system](../02_reference/quick_reference/type_system.md) | 实现简易数据结构 |
| **Week 4: 错误处理 + 泛型** | Book Ch 9-10 + RBE Error Handling | [error_handling_cheatsheet](../02_reference/quick_reference/error_handling_cheatsheet.md) | 重构错误处理 |
| **Week 5: 项目实战** | Book Ch 12 I/O Project | [CLI_APPLICATIONS_GUIDE](../05_guides/CLI_APPLICATIONS_GUIDE.md) | 完成命令行工具 |
| **Week 6: 复习 + 测试** | Book Ch 11 Testing | [testing_cheatsheet](../02_reference/quick_reference/testing_cheatsheet.md) | 为项目添加测试 |

### 路径二：中级进阶路径（能写项目 → 深入理解）

**预计时间**: 6-8 周

| 阶段 | 官方资源 | 本项目补充 | 练习 |
|------|---------|-----------|------|
| **Week 1: 智能指针深入** | Book Ch 15 | [smart_pointers_cheatsheet](../02_reference/quick_reference/smart_pointers_cheatsheet.md) | 实现自定义智能指针 |
| **Week 2: 并发基础** | Book Ch 16 + RBE Threads | [threads_concurrency_cheatsheet](../02_reference/quick_reference/threads_concurrency_cheatsheet.md) | 线程池实现 |
| **Week 3: 异步编程** | Book Ch 17 | [async_patterns](../02_reference/quick_reference/async_patterns.md) | 异步 Web 服务器 |
| **Week 4: Trait 系统深度** | Book Ch 10.2 + Reference Traits | [type_system](../02_reference/quick_reference/type_system.md) § 高级 | 复杂 trait 设计 |
| **Week 5: 宏系统** | Book Ch 20.5 + RBE macro_rules! | [macros_cheatsheet](../02_reference/quick_reference/macros_cheatsheet.md) | 编写 DSL |
| **Week 6: 设计模式** | Book Ch 18 OOP | [design_patterns](../../crates/c09_design_pattern/docs/README.md) | 实现经典模式 |
| **Week 7: 性能优化** | Book Ch 13.4 + Reference Types | [collections_iterators_cheatsheet](../02_reference/quick_reference/collections_iterators_cheatsheet.md) § 性能 | 性能调优实践 |
| **Week 8: Unsafe 基础** | Book Ch 20.1 | [UNSAFE_RUST_GUIDE](../05_guides/UNSAFE_RUST_GUIDE.md) § 基础 | FFI 绑定 |

### 路径三：高级专家路径（深入原理 → 形式化理解）

**预计时间**: 持续学习

| 阶段 | 官方资源 | 本项目补充 | 目标 |
|------|---------|-----------|------|
| **阶段1: 形式化基础** | Reference Type System | [variance_theory](../research_notes/type_theory/variance_theory.md) | 理解型变理论 |
| **阶段2: 所有权证明** | Reference Memory Model | [ownership_model](../research_notes/formal_methods/ownership_model.md) | 形式化所有权 |
| **阶段3: 并发安全证明** | Reference Send/Sync | [send_sync_formalization](../research_notes/formal_methods/send_sync_formalization.md) | 数据竞争自由证明 |
| **阶段4: 异步形式化** | Reference Coroutines | [async_state_machine](../research_notes/formal_methods/async_state_machine.md) | 状态机语义 |
| **阶段5: Unsafe 深入** | Reference Unsafety | [UNSAFE_RUST_GUIDE](../05_guides/UNSAFE_RUST_GUIDE.md) + [Rustonomicon](https://doc.rust-lang.org/nomicon/) | UB 边界掌握 |
| **阶段6: 编译器研究** | [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/) | [PROOF_INDEX](../research_notes/PROOF_INDEX.md) | 贡献 Rust 编译器 |

---

## 速查索引

### 按主题索引

| 主题 | 官方章节 | 本项目速查 | 形式化文档 |
|------|---------|-----------|-----------|
| **所有权** | Book Ch 4 | [ownership_cheatsheet](../02_reference/quick_reference/ownership_cheatsheet.md) | [ownership_model](../research_notes/formal_methods/ownership_model.md) |
| **借用** | Book Ch 4.2 | [ownership_cheatsheet](../02_reference/quick_reference/ownership_cheatsheet.md) | [borrow_checker_proof](../research_notes/formal_methods/borrow_checker_proof.md) |
| **生命周期** | Book Ch 10.3 | [type_system](../02_reference/quick_reference/type_system.md) | [variance_theory](../research_notes/type_theory/variance_theory.md) |
| **类型系统** | Book Ch 3.2, 10 | [type_system](../02_reference/quick_reference/type_system.md) | [PROOF_INDEX](../research_notes/PROOF_INDEX.md) |
| **Trait** | Book Ch 10.2 | [type_system](../02_reference/quick_reference/type_system.md) § Traits | - |
| **泛型** | Book Ch 10.1 | [generics_cheatsheet](../02_reference/quick_reference/generics_cheatsheet.md) | - |
| **并发** | Book Ch 16 | [threads_concurrency_cheatsheet](../02_reference/quick_reference/threads_concurrency_cheatsheet.md) | [send_sync_formalization](../research_notes/formal_methods/send_sync_formalization.md) |
| **异步** | Book Ch 17 | [async_patterns](../02_reference/quick_reference/async_patterns.md) | [async_state_machine](../research_notes/formal_methods/async_state_machine.md) |
| **错误处理** | Book Ch 9 | [error_handling_cheatsheet](../02_reference/quick_reference/error_handling_cheatsheet.md) | - |
| **宏** | Book Ch 20.5 | [macros_cheatsheet](../02_reference/quick_reference/macros_cheatsheet.md) | - |
| **Unsafe** | Book Ch 20.1 | [UNSAFE_RUST_GUIDE](../05_guides/UNSAFE_RUST_GUIDE.md) | - |
| **模式匹配** | Book Ch 19 | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md) § 模式 | - |
| **集合** | Book Ch 8 | [collections_iterators_cheatsheet](../02_reference/quick_reference/collections_iterators_cheatsheet.md) | - |
| **迭代器** | Book Ch 13.2 | [collections_iterators_cheatsheet](../02_reference/quick_reference/collections_iterators_cheatsheet.md) § Iterator | - |
| **闭包** | Book Ch 13.1 | [closures_cheatsheet](../02_reference/quick_reference/closures_cheatsheet.md) | - |
| **智能指针** | Book Ch 15 | [smart_pointers_cheatsheet](../02_reference/quick_reference/smart_pointers_cheatsheet.md) | - |
| **测试** | Book Ch 11 | [testing_cheatsheet](../02_reference/quick_reference/testing_cheatsheet.md) | - |
| **Cargo** | Book Ch 14 | [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) | - |

### 按官方章节快速跳转

| Book 章节 | 快速链接 | 本项目文档 |
|-----------|---------|-----------|
| Ch 1 - Getting Started | [Book](https://doc.rust-lang.org/book/ch01-00-getting-started.html) | [LEARNING_PATH_PLANNING.md](./LEARNING_PATH_PLANNING.md) |
| Ch 4 - Ownership | [Book](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) | [ownership_cheatsheet](../02_reference/quick_reference/ownership_cheatsheet.md) |
| Ch 8 - Collections | [Book](https://doc.rust-lang.org/book/ch08-00-common-collections.html) | [collections_iterators_cheatsheet](../02_reference/quick_reference/collections_iterators_cheatsheet.md) |
| Ch 9 - Error Handling | [Book](https://doc.rust-lang.org/book/ch09-00-error-handling.html) | [error_handling_cheatsheet](../02_reference/quick_reference/error_handling_cheatsheet.md) |
| Ch 10 - Generics/Traits | [Book](https://doc.rust-lang.org/book/ch10-00-generics.html) | [generics_cheatsheet](../02_reference/quick_reference/generics_cheatsheet.md) |
| Ch 11 - Testing | [Book](https://doc.rust-lang.org/book/ch11-00-testing.html) | [testing_cheatsheet](../02_reference/quick_reference/testing_cheatsheet.md) |
| Ch 13 - Iterators/Closures | [Book](https://doc.rust-lang.org/book/ch13-00-functional-features.html) | [closures_cheatsheet](../02_reference/quick_reference/closures_cheatsheet.md) |
| Ch 15 - Smart Pointers | [Book](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html) | [smart_pointers_cheatsheet](../02_reference/quick_reference/smart_pointers_cheatsheet.md) |
| Ch 16 - Concurrency | [Book](https://doc.rust-lang.org/book/ch16-00-concurrency.html) | [threads_concurrency_cheatsheet](../02_reference/quick_reference/threads_concurrency_cheatsheet.md) |
| Ch 17 - Async | [Book](https://doc.rust-lang.org/book/ch17-00-async-await.html) | [async_patterns](../02_reference/quick_reference/async_patterns.md) |
| Ch 20 - Advanced/Unsafe | [Book](https://doc.rust-lang.org/book/ch20-00-advanced-features.html) | [UNSAFE_RUST_GUIDE](../05_guides/UNSAFE_RUST_GUIDE.md) |

### 按 Rust by Example 主题索引

| RBE 主题 | 快速链接 | 本项目对应 |
|---------|---------|-----------|
| 3. Custom Types | [RBE](https://doc.rust-lang.org/rust-by-example/custom_types.html) | [type_system](../02_reference/quick_reference/type_system.md) |
| 8. Flow of Control | [RBE](https://doc.rust-lang.org/rust-by-example/flow_control.html) | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md) |
| 9. Functions | [RBE](https://doc.rust-lang.org/rust-by-example/fn.html) | [closures_cheatsheet](../02_reference/quick_reference/closures_cheatsheet.md) |
| 14. Generics | [RBE](https://doc.rust-lang.org/rust-by-example/generics.html) | [generics_cheatsheet](../02_reference/quick_reference/generics_cheatsheet.md) |
| 15. Scoping Rules | [RBE](https://doc.rust-lang.org/rust-by-example/scope.html) | [ownership_cheatsheet](../02_reference/quick_reference/ownership_cheatsheet.md) |
| 16. Traits | [RBE](https://doc.rust-lang.org/rust-by-example/trait.html) | [type_system](../02_reference/quick_reference/type_system.md) |
| 17. macro_rules! | [RBE](https://doc.rust-lang.org/rust-by-example/macros.html) | [macros_cheatsheet](../02_reference/quick_reference/macros_cheatsheet.md) |
| 18. Error Handling | [RBE](https://doc.rust-lang.org/rust-by-example/error.html) | [error_handling_cheatsheet](../02_reference/quick_reference/error_handling_cheatsheet.md) |
| 20. Std Misc (Threads) | [RBE](https://doc.rust-lang.org/rust-by-example/std_misc/threads.html) | [threads_concurrency_cheatsheet](../02_reference/quick_reference/threads_concurrency_cheatsheet.md) |
| 21. Testing | [RBE](https://doc.rust-lang.org/rust-by-example/testing.html) | [testing_cheatsheet](../02_reference/quick_reference/testing_cheatsheet.md) |
| 22. Unsafe | [RBE](https://doc.rust-lang.org/rust-by-example/unsafe.html) | [UNSAFE_RUST_GUIDE](../05_guides/UNSAFE_RUST_GUIDE.md) |

---

## 小节级映射与「本项目补充」

| 官方章节 | 小节 | 本项目补充内容 |
| :--- | :--- | :--- |
| **Book Ch 10** | 10.1-10.3 Traits, Lifetimes | 型变理论、生命周期形式化（[research_notes](../research_notes/README.md)）；转换树 |
| **Reference** | Types, Ownership, Special Types | 形式化工程系统（[rust-formal-engineering-system](../rust-formal-engineering-system/README.md)）；variance 专项 |
| **Reference** | Macros by Example, Procedural Macros | 宏系统决策树、反例（[macros_cheatsheet](../02_reference/quick_reference/macros_cheatsheet.md)） |
| **Book Ch 17** | 17.1-17.6 Async | 空 Future、持锁跨 await 反例（[async_patterns](../02_reference/quick_reference/async_patterns.md)）；EDGE_CASES |
| **Book Ch 3** | 3.1-3.5 Types, Control Flow | 控制流（[C03](../../crates/c03_control_fn/docs/README.md)）；模式匹配决策树 |
| **Book Ch 9** | 9.1-9.3 Error Handling | 错误传播转换树（[THINKING_REPRESENTATION_METHODS](../04_thinking/THINKING_REPRESENTATION_METHODS.md)）；[error_handling_cheatsheet](../02_reference/quick_reference/error_handling_cheatsheet.md) |
| **Book Ch 11** | 11.1-11.3 Testing | [testing_cheatsheet](../02_reference/quick_reference/testing_cheatsheet.md)；#[test] 1.93 严格化（[09_compatibility_deep_dive](../06_toolchain/09_rust_1.93_compatibility_deep_dive.md)） |
| **Reference** | Attributes, Macros | offset_of! 类型检查（1.93）；[macros_cheatsheet](../02_reference/quick_reference/macros_cheatsheet.md) |
| **Reference** | Type system, Variance | [variance_theory](../research_notes/type_theory/variance_theory.md)；[PROOF_INDEX](../research_notes/PROOF_INDEX.md) |
| **releases.rs** | 1.93 Language/Libraries | [09_rust_1.93_compatibility_deep_dive](../06_toolchain/09_rust_1.93_compatibility_deep_dive.md)；[07_full_changelog](../06_toolchain/07_rust_1.93_full_changelog.md) |

> 标注「本项目补充」表示官方资源未覆盖或简略，本项目提供额外深度。

---

## 核心概念映射

| 概念 | 本项目速查卡 | Book 章节 | RBE |
| :--- | :--- | :--- | :--- |
| 借用 | ownership_cheatsheet | Ch 4.2 | [Borrow](https://doc.rust-lang.org/rust-by-example/scope/borrow.html) |
| 生命周期 | type_system | Ch 10.3 | [Lifetime](https://doc.rust-lang.org/rust-by-example/scope/lifetime.html) |
| Trait | type_system | Ch 10 | [Traits](https://doc.rust-lang.org/rust-by-example/trait.html) |
| 错误处理 | error_handling_cheatsheet | Ch 9 | [Error](https://doc.rust-lang.org/rust-by-example/error.html) |
| 泛型 | generics_cheatsheet | Ch 10.1 | [Generics](https://doc.rust-lang.org/rust-by-example/generics.html) |
| 异步 | async_patterns | Ch 17 | [Async](https://doc.rust-lang.org/rust-by-example/async.html) |
| 测试 | testing_cheatsheet | Ch 11 | [Testing](https://doc.rust-lang.org/rust-by-example/testing.html) |

---

## RBE 练习与 Rustlings 映射

- **RBE 练习**：上表「RBE 练习（可点击）」列提供各模块对应的 RBE 章节链接，可直接点击进入练习
- **Rustlings 模块映射**：[exercises/RUSTLINGS_MAPPING.md](../../exercises/RUSTLINGS_MAPPING.md) — C01–C12 与 Rustlings 习题主题对应表（含可点击 GitHub 链接）

---

## 📋 官方资源使用场景指南

### 学习场景对照表

| 你的情况 | 推荐资源 | 使用方式 |
| :--- | :--- | :--- |
| 完全零基础 | The Rust Book | 按章节顺序阅读，完成每章练习 |
| 有其他编程经验 | Rust by Example + Book | 先看 RBE 快速上手，再深入 Book |
| 需要快速查阅语法 | Standard Library 文档 | 使用搜索功能查找具体 API |
| 准备面试/考试 | Brown 交互版 Book | 完成所有测验，查看可视化解释 |
| 喜欢动手练习 | Rustlings | 按提示修复代码，循序渐进 |
| 遇到编译错误 | Compiler Error Index | 搜索错误码，阅读详细解释 |
| 开发 CLI 应用 | Command Line Book | 参考项目结构和最佳实践 |
| 嵌入式开发 | Embedded Rust Book | 学习 no_std 和硬件交互 |

---

## 🌳 资源选择决策树

```text
开始选择学习资源
    │
    ├── 你是 Rust 新手？
    │       │
    │       ├── 是 → 有编程基础？
    │       │           │
    │       │           ├── 是 → 想快速上手？
    │       │           │           │
    │       │           │           ├── 是 → Rust by Example
    │       │           │           │
    │       │           │           └── 否 → The Rust Book
    │       │           │
    │       │           └── 否 → The Rust Book（仔细阅读）
    │       │
    │       └── 否 → 需要解决具体问题？
    │                   │
    │                   ├── 是 → 编译错误？
    │                   │           │
    │                   │           ├── 是 → Compiler Error Index
    │                   │           │
    │                   │           └── 否 → Standard Library 文档
    │                   │
    │                   └── 否 → 深入学习？
    │                               │
    │                               ├── 是 → Rust Reference
    │                               │
    │                               └── 否 → releases.rs 了解新特性
    │
    └── 需要练习？
            │
            ├── 是 → 喜欢命令行交互？
            │           │
            │           ├── 是 → Rustlings
            │           │
            │           └── 否 → Brown 交互版 Book
            │
            └── 否 → 查看场景对照表选择
```

---

## 🎯 按目标选择资源

### 目标: 通过 Rust 面试

**推荐路径**:

1. [Brown 交互版 Book](https://rust-book.cs.brown.edu/) - 完成所有测验
2. [Rustlings](https://github.com/rust-lang/rustlings) - 完成 80% 以上练习
3. [Compiler Error Index](https://doc.rust-lang.org/error-index.html) - 熟悉常见错误

### 目标: 开发生产项目

**推荐路径**:

1. [The Rust Book](https://doc.rust-lang.org/book/) - 完整阅读
2. [Rust Reference](https://doc.rust-lang.org/reference/) - 查阅语言规范
3. [Command Line Book](https://rust-cli.github.io/book/) - CLI 项目
4. [Rustonomicon](https://doc.rust-lang.org/nomicon/) - unsafe 代码

### 目标: 贡献 Rust 编译器

**推荐路径**:

1. [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/) - 编译器开发指南
2. [Rust Reference](https://doc.rust-lang.org/reference/) - 理解语言规范
3. [Ferrocene FLS](https://spec.ferrocene.dev/) - 形式化规范

### 目标: 学术研究（形式化验证）

**推荐路径**:

1. [RustBelt 论文](https://plv.mpi-sws.org/rustbelt/popl18/) - 理论基础
2. [Ferrocene FLS](https://spec.ferrocene.dev/) - 形式化规范
3. 本项目 [formal_methods](../research_notes/formal_methods/README.md) - 中文形式化论证

---

## 🎓 高校课程资源映射（权威对齐）

### Stanford

| 课程 | 链接 | 主要内容 | 本项目对应 |
| :--- | :--- | :--- | :--- |
| **CS340R: Rusty Systems** | <https://web.stanford.edu/class/cs340r/> | Rust 系统编程、3 周基础 + 7 周系统重实现项目 | [05_guides/](../05_guides/README.md)、[C05 线程](../02_reference/quick_reference/threads_concurrency_cheatsheet.md)、[C10 网络](../02_reference/quick_reference/network_programming_cheatsheet.md) |

### CMU

| 课程 | 链接 | 主要内容 | 本项目对应 |
| :--- | :--- | :--- | :--- |
| **17-363/17-663: Programming Language Pragmatics** | <https://www.cs.cmu.edu/~aldrich/courses/17-363/> | 编程语言基础、约 4/8 作业用 Rust 实现编译器 | [C11 宏](../02_reference/quick_reference/macros_cheatsheet.md)、[C02 类型系统](../02_reference/quick_reference/type_system.md) |
| **17-770: WebAssembly** | <https://www.cs.cmu.edu/~wasm/cs17-770/> | WebAssembly 引擎，支持 Rust 实现 | [C12 WASM](../02_reference/quick_reference/wasm_cheatsheet.md) |

### 其他高校（参考）

| 课程 | 机构 | 链接 | 说明 |
| :--- | :--- | :--- | :--- |
| **CIS 1905: Rust Programming** | UPenn | <https://www.cis.upenn.edu/~cis1905/> | 所有权、内存安全、数据竞争自由、并行与异步 |

> **说明**：MIT 暂无公开的 Rust 专项课程；上述课程为 2024–2025 学年可查资源，具体开课情况以各校官网为准。

---

## 🔗 形式化文档链接

### 形式化证明体系（2026-02-14）

| 资源 | 说明 | 形式化链接 |
| :--- | :--- | :--- |
| [FORMAL_PROOF_SYSTEM_GUIDE](../research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md) | 批判性分析与推进计划 | [formal_methods/README](../research_notes/formal_methods/README.md) |
| [CORE_THEOREMS_FULL_PROOFS](../research_notes/CORE_THEOREMS_FULL_PROOFS.md) | 核心定理完整证明（L2） | [ownership_model](../research_notes/formal_methods/ownership_model.md)、[borrow_checker_proof](../research_notes/formal_methods/borrow_checker_proof.md) |
| [INTERNATIONAL_FORMAL_VERIFICATION_INDEX](../research_notes/INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) | 国际对标 | [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)、[Ferrocene FLS](https://spec.ferrocene.dev/) |

### 官方形式化资源映射

| 官方资源 | 本项目形式化文档 |
| :--- | :--- |
| [Ferrocene FLS - Ch.5 Patterns](https://spec.ferrocene.dev/patterns.html) | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md) |
| [Ferrocene FLS - Ch.15 Ownership](https://spec.ferrocene.dev/ownership-and-deconstruction.html) | [ownership_model](../research_notes/formal_methods/ownership_model.md) |
| [Ferrocene FLS - Ch.15 Borrowing](https://spec.ferrocene.dev/ownership-and-deconstruction.html#borrowing) | [borrow_checker_proof](../research_notes/formal_methods/borrow_checker_proof.md) |
| [Ferrocene FLS - Ch.16 Exceptions](https://spec.ferrocene.dev/exceptions-and-errors.html) | [error_handling_cheatsheet](../02_reference/quick_reference/error_handling_cheatsheet.md) |
| [Ferrocene FLS - Ch.17 Concurrency](https://spec.ferrocene.dev/concurrency.html) | [send_sync_formalization](../research_notes/formal_methods/send_sync_formalization.md)、[async_state_machine](../research_notes/formal_methods/async_state_machine.md) |
| [Ferrocene FLS - Ch.19 Unsafety](https://spec.ferrocene.dev/unsafety.html) | [UNSAFE_RUST_GUIDE](../05_guides/UNSAFE_RUST_GUIDE.md) |
| [Ferrocene FLS - Ch.21 FFI](https://spec.ferrocene.dev/ffi.html) | [UNSAFE_RUST_GUIDE](../05_guides/UNSAFE_RUST_GUIDE.md) § FFI |
| [Ferrocene FLS - Appendix C UB](https://spec.ferrocene.dev/undefined-behavior.html) | [EDGE_CASES_AND_SPECIAL_CASES](../02_reference/EDGE_CASES_AND_SPECIAL_CASES.md) |
| [Rust Reference - Undefined Behavior](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) | [EDGE_CASES_AND_SPECIAL_CASES](../02_reference/EDGE_CASES_AND_SPECIAL_CASES.md) |

---

## 在线课程资源映射（edX + Coursera）

### edX 课程与项目内容对齐

| 课程 | 机构 | 链接 | 主要内容 | 本项目对应路径 |
| :--- | :--- | :--- | :--- | :--- |
| Introduction to Rust Programming | Microsoft | <https://www.edx.org/learn/rust/microsoft-introduction-to-rust-programming> | Rust语法基础、所有权、类型系统 | [01_learning/](./README.md) - C01-C04 基础阶段 |
| Rust for Developers | Linux Foundation | <https://www.edx.org/learn/rust/the-linux-foundation-rust-for-developers> | 实战开发、项目构建、最佳实践 | [05_guides/](../05_guides/README.md) - 开发指南 |
| Programming with Rust | W3C | <https://www.edx.org/learn/rust/w3cx-programming-with-rust> | 语法速查、模式匹配、标准库 | [02_reference/quick_reference/](../02_reference/quick_reference/README.md) - 速查卡 |

### Coursera 课程与项目内容对齐

| 课程 | 机构 | 链接 | 主要内容 | 本项目对应路径 |
| :--- | :--- | :--- | :--- | :--- |
| Rust Fundamentals | Duke | <https://www.coursera.org/learn/rust-fundamentals> | 所有权、借用、生命周期、enum、struct、trait、泛型 | [ownership_cheatsheet](../02_reference/quick_reference/ownership_cheatsheet.md)、[type_system](../02_reference/quick_reference/type_system.md) |
| Rust Programming Essentials | Edureka | <https://www.coursera.org/learn/rust-programming-essentials> | 模式匹配、所有权、类型系统、Cargo | [control_flow_functions_cheatsheet](../02_reference/quick_reference/control_flow_functions_cheatsheet.md)、[cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) |
| Advanced Rust Programming | Edureka | <https://www.coursera.org/learn/advanced-rust-programming> | 并发、多线程、内存管理、集合、trait、泛型 | [threads_concurrency_cheatsheet](../02_reference/quick_reference/threads_concurrency_cheatsheet.md)、[collections_iterators_cheatsheet](../02_reference/quick_reference/collections_iterators_cheatsheet.md) |
| Rust Programming Specialization | Duke | <https://www.coursera.org/specializations/rust-programming> | 系统编程、数据工程、Linux、DevOps、LLM、云、MLOps | [05_guides/](../05_guides/README.md)、[CLI_APPLICATIONS_GUIDE](../05_guides/CLI_APPLICATIONS_GUIDE.md) |

### 学习路径建议

**初学者路径** (Microsoft课程 → 本项目):

1. 完成 edX Microsoft 入门课程
2. 结合本项目 [LEARNING_PATH_PLANNING.md](./LEARNING_PATH_PLANNING.md) 深化理解
3. 通过 [Rustlings 练习](../../exercises/RUSTLINGS_MAPPING.md) 巩固知识

**开发者进阶路径** (Linux Foundation课程 → 本项目):

1. 完成 edX Linux Foundation 开发者课程
2. 参考本项目 [05_guides/](../05_guides/README.md) 专题指南
3. 阅读 [异步模式速查](../02_reference/quick_reference/async_patterns.md) 等进阶内容

---

## 相关文档

- [文档中心](../README.md)
- [学习路径规划](./LEARNING_PATH_PLANNING.md)
- [Rustlings 映射](../../exercises/RUSTLINGS_MAPPING.md)
- [形式化方法研究](../research_notes/formal_methods/README.md)
- [类型理论研究](../research_notes/type_theory/README.md)

---

## 🆕 Rust 1.94 学习路径

> **适用版本**: Rust 1.94.0+

### 1.94 新特性学习要点

| 特性 | 学习难度 | 推荐顺序 |
|------|---------|---------|
| rray_windows | ⭐ | 第1周 |
| ControlFlow | ⭐⭐ | 第2周 |
| LazyCell/LazyLock 新方法 | ⭐⭐ | 第3周 |
| Peekable::next_if_map | ⭐ | 第4周 |

### 学习资源

- [Rust 1.94 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 发布说明](../06_toolchain/16_rust_1.94_release_notes.md)

**最后更新**: 2026-03-14 (添加 Rust 1.94 学习路径)

---

## 🆕 Rust 1.94 深度整合更新

> **适用版本**: Rust 1.94.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档

- [Rust 1.94 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 特性速查](../02_reference/quick_reference/rust_194_features_cheatsheet.md)
- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-14 (Rust 1.94 深度整合)
