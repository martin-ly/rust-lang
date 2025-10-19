# Rust 1.90 语言特性与基础语法（全面指南）

面向 Rust 1.90 的系统化中文指南：覆盖基础语法、规范用法、最佳实践与可编译示例。本文聚焦“在 1.90 版本中可用的语言特性全集”（而非仅新增项），便于在生产与教学中统一参考。

## 目录

- [Rust 1.90 语言特性与基础语法（全面指南）](#rust-190-语言特性与基础语法全面指南)
  - [目录](#目录)
  - [1. 基础语法与约定](#1-基础语法与约定)
  - [2. 所有权、借用与生命周期](#2-所有权借用与生命周期)
  - [3. 泛型、Trait 约束与 where 子句](#3-泛型trait-约束与-where-子句)
  - [4. 关联类型、GATs、HRTBs](#4-关联类型gatshrtbs)
  - [5. 常量泛型（Const Generics）](#5-常量泛型const-generics)
  - [6. 模块系统、可见性与路径](#6-模块系统可见性与路径)
  - [7. 模式匹配与解构](#7-模式匹配与解构)
  - [8. 闭包、迭代器与集合](#8-闭包迭代器与集合)
  - [9. 错误处理：Result、thiserror、anyhow](#9-错误处理resultthiserroranyhow)
  - [10. 并发模型：Send/Sync、线程、并行](#10-并发模型sendsync线程并行)
  - [11. Trait 上行转换（Trait Object Upcasting）](#11-trait-上行转换trait-object-upcasting)
  - [12. 异步编程：async/await、Future](#12-异步编程asyncawaitfuture)
  - [13. 智能指针与内存模型](#13-智能指针与内存模型)
  - [14. 宏系统：声明宏与过程宏（derive）](#14-宏系统声明宏与过程宏derive)
  - [15. 属性与内置属性](#15-属性与内置属性)
  - [16. 关联常量与默认值](#16-关联常量与默认值)
  - [17 Unsafe 基础与 FFI 轮廓](#17-unsafe-基础与-ffi-轮廓)
  - [18 规范与风格](#18-规范与风格)
  - [19. 关联常量与默认值](#19-关联常量与默认值)
  - [20. 关联类型的 where 约束](#20-关联类型的-where-约束)
  - [20. 工业实践](#20-工业实践)
  - [21. 学习与调试](#21-学习与调试)
  - [22. 微基准测试](#22-微基准测试)

> 对应源码：`src/rust_190_features.rs`（含大量带中文详注的最小可运行示例）。

---

## 1. 基础语法与约定

- 变量与可变性：`let`/`let mut`，尽量最小可变域；
- 常量：`const` 用于编译期常量，`static` 用于全局静态；
- 表达式导向：`if`/`match`/块表达式都返回值；
- 基本类型与字面量：整型、浮点、布尔、字符、切片与字符串；
- 注释：行注释 `//`，文档注释 `///`；
- 命名：类型与模块使用驼峰/蛇形规范，公共 API 注重语义与稳定性。

示例：

```rust
let answer: i32 = 42;
let mut counter = 0;
counter += 1;
```

## 2. 所有权、借用与生命周期

- 移动与拷贝：遵循 `Copy` 语义的标量类型可隐式复制；
- 借用：`&T` 共享、`&mut T` 独占；
- 悬垂引用被编译器禁止；
- 生命周期省略规则简化大部分签名；
- RAII：`Drop` 自动资源回收。

## 3. 泛型、Trait 约束与 where 子句

- 泛型函数/类型：`fn f<T: Trait>(t: T)`；
- 约束写法：尖括号或 `where` 子句；
- 多 Trait 组合、关联常量与默认方法实现。

## 4. 关联类型、GATs、HRTBs

- 关联类型：在 trait 中为相关类型命名；
- GATs：在关联类型上使用泛型参数；
- HRTBs：`for<'a>` 高阶生命周期界定，用于闭包/函数指针。
- 示例：`apply_to_slices` 接收 `for<'a> Fn(&'a [u8]) -> usize`，见 `src/rust_190_features.rs`。
- GATs 示例：`BufLines::Lines<'a>` 将关联类型与输入借用生命周期绑定，见 `src/rust_190_features.rs`。

## 5. 常量泛型（Const Generics）

- 使用编译期常量参数构造静态容量容器、位宽算法等；
- 与 `where`、特征约束结合，表达更强静态保证。
- 示例：`RingBuffer<T, const N: usize>` 与 `FixedArray<T, N>` 结合关联常量阈值判断，见 `src/rust_190_features.rs`。

## 6. 模块系统、可见性与路径

- 模块与路径：`mod`、`pub`、`crate::`、`super::`、`self::`；
- 重导出与门面（facade）：`pub use`；
- 分层设计与清晰边界。
- 示例：`visibility_demo` 展示 `pub(crate)`, `pub(super)` 与重导出，见 `src/rust_190_features.rs`。
- API 门面：内部版本 `api_internal_v1/v2`，通过 `pub mod api { pub use ... }` 暴露稳定 API，见 `src/rust_190_features.rs`。

## 7. 模式匹配与解构

- `match` 完备性检查；
- `if let`/`while let` 精炼分支；
- 结构体/枚举/元组/切片解构。

## 8. 闭包、迭代器与集合

- 闭包捕获与类型推断；
- Iterator 组合与零成本抽象；
- `itertools` 扩展适配器。
- 迭代器返回位置 `impl Trait`（RPITIT）：在 trait 方法中返回实现 `Iterator` 的匿名类型，示例 `NumberSource::numbers`，见 `src/rust_190_features.rs`。
- 高级组合：无装箱管道（RPITIT）与装箱（`Box<dyn Iterator>`）对比：`Data::pipeline` vs `boxed_pipeline`，见 `src/rust_190_features.rs`。

## 9. 错误处理：Result、thiserror、anyhow

- `Result<T, E>` 与 `?` 传播；
- 自定义错误（`thiserror`），应用层封装（`anyhow`）。
- 分层错误建模：底层 `IoLayerError`、上层 `ConfigLayerError`，通过 `#[from]` 与透明错误传递组合；见 `read_config_len` 示例（`src/rust_190_features.rs`）。

## 10. 并发模型：Send/Sync、线程、并行

- 通过 `Send/Sync` 建模跨线程安全；
- `rayon` 数据并行；
- 原子与锁的选择与代价。
- 共享状态：`Arc<Mutex<T>>`（写多时简单可用）与 `Arc<RwLock<T>>`（读多写少时友好）对比；见 `shared_state_demo`，`src/rust_190_features.rs`。

## 11. Trait 上行转换（Trait Object Upcasting）

- 当 `Sub: Super` 时，`&dyn Sub` 可上行转换为 `&dyn Super`；同理 `Box<dyn Sub> -> Box<dyn Super>`。
- 示例：`AdvancedLogger: Logger`，将 `&dyn AdvancedLogger` 上行转换为 `&dyn Logger`，见 `src/rust_190_features.rs`。
- 扩展：`upcast_box`, `upcast_arc` 展示 Box/Arc 上行转换与用法，见 `src/rust_190_features.rs`。

## 12. 异步编程：async/await、Future

- `async fn` 与 `Future`；
- 执行器与 I/O 模型（概念性介绍）。
- 示例：`async_add_generic` 返回位置 `impl Future`，以及最小 `block_on` 实现，见 `src/rust_190_features.rs`。
- 共享状态：对比 `Arc<Mutex<T>>` 与 `Arc<RwLock<T>>` 的权衡（建议示例在并发章节中补充）。

## 13. 智能指针与内存模型

- `Box`, `Rc`, `Arc`, `RefCell`, `Mutex` 等；
- 所有权边界下的共享与可变性管理。

## 14. 宏系统：声明宏与过程宏（derive）

- `macro_rules!` 模式匹配；
- `#[derive(...)]` 与生态宏的工程化使用。
- 示例：`make_vec!` 声明宏与 `#[derive(Debug, Clone, PartialEq)]` 的 `Point`，见 `src/rust_190_features.rs`。
- 宏批量实现：`impl_to_i64_for!` 为多种数值类型批量实现 `ToI64`，见 `src/rust_190_features.rs`。
- 过程宏：自定义 `#[derive(Display, WithId)]` 示例，见 `proc_macro_derive/` 子 crate 与 `User` 结构体，`src/rust_190_features.rs`。

## 15. 属性与内置属性

- 条件编译 `#[cfg]`；
- 内联与内联提示 `#[inline]`；
- 文档化 `#[doc]` 与可见性控制。
- 示例：`#[inline]` 的 `add_inline`，见 `src/rust_190_features.rs`。

## 16. 关联常量与默认值

## 17 Unsafe 基础与 FFI 轮廓

- `unsafe` 的五类操作；
- 与 C 交互的最小示例轮廓与安全封装建议。
- 示例：`#[repr(C)] CPoint` 与原始指针只读访问的安全封装 `distance_sq_safe/distance_sq_owned`，见 `src/rust_190_features.rs`。

## 18 规范与风格

## 19. 关联常量与默认值

- 在 trait 中定义 `const`，可提供默认值，由具体实现覆盖；
- 与常量泛型配合实现静态阈值/尺寸策略。
- 示例：`HasThreshold`、`FixedArray<i32, N>` 覆盖阈值为 `N*2`，见 `src/rust_190_features.rs`。

## 20. 关联类型的 where 约束

- 在方法上为关联类型消费者增加 `where` 约束，例如 `Serializer::serialize<T>` 要求 `T: Serialize`；
- 可将输出 `type Output` 与不同实现绑定（如 JSON 输出 `String`）。
- 示例：`Serializer`/`JsonSerializer`，见 `src/rust_190_features.rs`。

---

运行示例与测试：

```bash
cargo test -q rust_190_features
```

定位到代码：

- `src/rust_190_features.rs` 中的模块化示例及测试用例
- 相关基础能力在 `src/basic_syntax.rs` 提供更完整的泛型、枚举、生命周期与模式

- 命名一致性与文档友好；
- 公共 API 的清晰语义与稳定性策略；
- 错误类型与边界的设计。

## 20. 工业实践

- 序列化/反序列化模型；
- 并行加速与可预估的性能轮廓；
- 错误建模与可观测性（日志/度量）。

## 21. 学习与调试

- `rustfmt`、`clippy`、`cargo test`、`cargo bench`；
- 断言、属性测试与简洁可验证的最小示例。

## 22. 微基准测试

- 迭代器管道性能对比：无装箱 vs 装箱实现；
- 并发锁策略对比：`Mutex` vs `RwLock` 在不同读写比例下的表现；
- 异步泛型函数性能基线。
- 运行基准：`cargo bench`，见 `benches/micro_benchmarks.rs`。

---

更多示例与详注请见源码 `src/rust_190_features.rs`，可通过 `cargo test -q rust_190_features` 快速验证运行。
