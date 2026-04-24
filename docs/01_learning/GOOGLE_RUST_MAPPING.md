# Google Comprehensive Rust 课程映射

> **创建日期**: 2026-04-24
> **用途**: 将 Google 4天 Rust 课程与本项目内容对接，标注差异与补充材料
> **课程来源**: <https://google.github.io/comprehensive-rust/>

---

## Google 课程模块概览

Google Comprehensive Rust 分为 4 天：

| 天数 | 主题 | 本项目对应 | 覆盖度 |
| :--- | :--- | :--- | :--- |
| Day 1 | 基础（类型、控制流、所有权） | `crates/c01`–`c03` | 100% |
| Day 2 | 复合类型（结构体、枚举、模式匹配） | `crates/c02` | 100% |
| Day 3 | 泛型、Trait、生命周期 | `crates/c04` | 100% |
| Day 4 | 深入主题（闭包、迭代器、并行、Unsafe） | `crates/c05`–`c13` | 90% |

---

## Day 1: Rust 基础

### Google 内容

- Hello World
- 变量与可变性
- 标量类型与复合类型
- 函数
- 控制流（if/else、loop、while、for）
- 所有权基础（栈 vs 堆、move、clone）
- 借用与引用
- 字符串与切片

### 本项目映射

| Google 主题 | 项目文件 | 差异/补充 |
| :--- | :--- | :--- |
| 变量与可变性 | `crates/c03_control_fn/src/basic_syntax.rs` | 本项目额外覆盖 shadowing、常量作用域 |
| 标量类型 | `crates/c02_type_system/src/primitive_types/scalar_types/` | 额外包含位操作、字节操作、增强整数类型 |
| 复合类型 | `crates/c02_type_system/src/primitive_types/compound_types/` | 额外包含数组高级用法、元组解构 |
| 函数 | `crates/c03_control_fn/src/function/` | 额外包含泛型函数、const fn、async fn |
| 控制流 | `crates/c03_control_fn/src/control_struct/` | 额外包含 Rust 1.94+ 控制流新特性 |
| 所有权 | `crates/c01_ownership_borrow_scope/src/ownership/` | **核心差异**: 本项目包含更深入的内存布局分析 |
| 借用 | `crates/c01_ownership_borrow_scope/src/borrow_checker/` | 额外包含 NLL、Polonius 概念介绍 |
| 字符串 | `crates/c02_type_system/src/primitive_types/scalar_types/string/` | 额外包含 String 性能优化指南 |

### 补充材料

- `docs/02_reference/quick_reference/ownership_cheatsheet.md` - 所有权速查
- `docs/02_reference/quick_reference/type_system.md` - 类型系统速查
- `exercises/src/ownership_borrowing/ex01_borrow_checker_fix.rs` - 练习

---

## Day 2: 复合类型与模式匹配

### Google 内容

- 结构体（命名字段、元组结构体、单元结构体）
- 枚举与方法
- 模式匹配（match、解构、守卫）
- Option<T> 与 Result<T, E>
- 方法语法（self、&self、&mut self）
- 泛型枚举

### 本项目映射

| Google 主题 | 项目文件 | 差异/补充 |
| :--- | :--- | :--- |
| 结构体 | `crates/c02_type_system/src/type_composition/composite/struct/` | 额外包含 零大小类型、对齐控制 |
| 枚举 | `crates/c02_type_system/src/type_composition/composite/enum/` | 额外包含 非穷尽枚举、判别值控制 |
| 模式匹配 | `crates/c02_type_system/src/type_decomposition/match/` | 额外包含 高级模式、@ 绑定、或模式 |
| Option / Result | `crates/c03_control_fn/src/error_handling/` | 额外包含 try trait、? 运算符在 Option 中的链式使用 |
| 方法语法 | `crates/c02_type_system/src/type_class/` | 额外包含 关联类型方法、泛型 impl 块 |

### 补充材料

- `docs/02_reference/quick_reference/design_patterns_cheatsheet.md` - 设计模式速查
- `exercises/src/type_system/ex01_enum_pattern_match.rs` - 练习
- `exercises/src/type_system/ex02_struct_methods.rs` - 练习

---

## Day 3: 泛型、Trait 与生命周期

### Google 内容

- 泛型函数与结构体
- Trait 定义与实现
- Trait Bounds
- 关联类型
- 生命周期基础
- 静态生命周期
- trait 对象（dyn Trait）

### 本项目映射

| Google 主题 | 项目文件 | 差异/补充 |
| :--- | :--- | :--- |
| 泛型 | `crates/c04_generic/src/basic_syntax.rs` | **核心差异**: 本项目包含 GAT、HRTB、泛型关联类型等高级内容 |
| Trait | `crates/c04_generic/src/trait_bound/` | 额外覆盖 所有标准库 trait 的独立讲解 |
| Trait Bounds | `crates/c04_generic/src/trait_bound/mod.rs` | 额外包含 复杂 where 子句、隐式 bound |
| 关联类型 | `crates/c04_generic/src/associated_type/` | 额外包含 GAT（泛型关联类型）完整示例 |
| 生命周期 | `crates/c01_ownership_borrow_scope/src/lifetime/` | 额外包含 生命周期子类型、复杂标注场景 |
| 静态生命周期 | `crates/c01_ownership_borrow_scope/src/lifetime/mod.rs` | 额外包含 `'static` vs `T: 'static` 区别 |
| Trait 对象 | `crates/c04_generic/src/polymorphism/trait_object.rs` | 额外包含 Object Safety 规则详解 |

### 差异说明

Google 课程在泛型与生命周期部分相对简洁。本项目的 **显著优势**：

1. **GAT (Generic Associated Types)**: `crates/c04_generic/src/advanced/gat_patterns.rs`
2. **HRTB (Higher-Ranked Trait Bounds)**: `crates/c04_generic/src/archive/rust_189_gat_hrtbs.rs`
3. **自然变换**: `crates/c04_generic/src/natural_transformation/`
4. **类型推断深度分析**: `crates/c04_generic/src/type_inference/`

### 补充材料

- `docs/02_reference/quick_reference/generics_cheatsheet.md` - 泛型速查
- `exercises/src/generics_traits/ex02_associated_types.rs` - 练习
- `exercises/src/type_system/ex05_trait_object.rs` - 练习

---

## Day 4: 深入主题

### Google 内容

- 闭包（Fn/FnMut/FnOnce）
- 迭代器（Iterator trait、适配器）
- Box<T>、Rc<T>、RefCell<T>
- 线程与通道
- Arc<T>、Mutex<T>
- Send 与 Sync
- Unsafe Rust 基础
- FFI 基础

### 本项目映射

| Google 主题 | 项目文件 | 差异/补充 |
| :--- | :--- | :--- |
| 闭包 | `crates/c03_control_fn/src/closure/` | 额外包含 闭包与设计模式、异步闭包 |
| 迭代器 | `docs/02_reference/quick_reference/collections_iterators_cheatsheet.md` | 额外包含 自定义迭代器、并行迭代器 |
| Box<T> | `crates/c01_ownership_borrow_scope/src/ownership/` | 额外包含 Box 内存布局 |
| Rc<T> | `crates/c01_ownership_borrow_scope/src/internal_mut/refcell/` | 额外包含 Weak<T>、循环引用处理 |
| RefCell<T> | `crates/c01_ownership_borrow_scope/src/internal_mut/refcell/` | 额外包含 运行时借用检查的内部实现 |
| 线程 | `crates/c05_threads/src/threads/` | **核心差异**: 本项目线程内容远超 Google 课程 |
| 通道 | `crates/c05_threads/src/message_passing/` | 额外包含 优先级通道、背压处理 |
| Arc<T> | `crates/c05_threads/src/synchronization/arc/` | 额外包含 Arc 内部原理 |
| Mutex<T> | `crates/c05_threads/src/synchronization/mutex/` | 额外包含 优先级继承、自适应锁 |
| Send/Sync | `crates/c04_generic/src/trait_bound/send.rs` | 额外包含 手动实现 Send/Sync |
| Unsafe Rust | `docs/03_guides/UNSAFE_RUST_GUIDE.md` | 额外包含 Miri 使用、UB 检测 |
| FFI | `docs/03_guides/FFI_PRACTICAL_GUIDE.md` | 额外包含 CXX 互操作、WASM FFI |

### 本项目超出的内容

Google 课程 Day 4 相对简洁，本项目在以下方面有显著扩展：

1. **异步编程**: `crates/c06_async/` 是整个独立 crate，远超 Google 课程内容
2. **设计模式**: `crates/c09_design_pattern/` 包含 Rust 特有的模式实现
3. **网络编程**: `crates/c10_networks/` 包含 HTTP、gRPC、WebSocket
4. **宏系统**: `crates/c11_macro_system/` 声明宏与过程宏
5. **WASM**: `crates/c12_wasm/` WebAssembly 开发
6. **嵌入式**: `crates/c13_embedded/` 裸机嵌入式开发
7. **算法**: `crates/c08_algorithms/` 包含并行与分布式算法

### 补充材料

- `docs/03_guides/THREADS_CONCURRENCY_USAGE_GUIDE.md` - 并发指南
- `docs/03_guides/ASYNC_PROGRAMMING_USAGE_GUIDE.md` - 异步指南
- `docs/03_guides/UNSAFE_PATTERNS_GUIDE.md` - Unsafe 模式

---

## Google 课程有但本项目缺少的内容

| 内容 | 说明 | 建议补充 |
| :--- | :--- | :--- |
| 错误处理最佳实践（Google 风格） | Google 有专门的错误处理章节 | 可参考 `docs/05_guides/BEST_PRACTICES.md` 扩充 |
| 测试策略（Google 内部） | Google 测试认证内容 | 可结合 `docs/03_guides/TEST_COVERAGE.md` |
| 工具链（cargo、clippy、rustfmt） | 相对基础 | 已有 `docs/02_reference/quick_reference/cargo_cheatsheet.md` |
| 标准库详细 API 讲解 | Google 按模块讲解 | 已有 `docs/02_reference/STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md` |

---

## 综合对比总结

| 维度 | Google 课程 | 本项目 |
| :--- | :--- | :--- |
| **目标受众** | 有编程经验的工程师 | 从入门到专家的全阶段 |
| **深度** | 4天速成，广度优先 | 模块化深入，可长期参考 |
| **实践** | 课堂练习 | 100+ 练习题、可运行示例、完整项目 |
| **并发** | 基础线程 + 锁 | 线程、无锁、异步、Actor、SIMD |
| **生态** | 提及主要 crate | 详细版本管理、workspace 实践 |
| **认证对接** | 无 | LFRS、Rustlings、Exercism 全对接 |
| **Rust 版本** | 更新较慢 | 跟踪 1.96+ nightly，包含最新特性 |

---

## 推荐学习路径

### 如果已完成 Google 课程

1. 使用本映射文档查漏补缺
2. 重点学习本项目**超出 Google 课程**的部分：
   - `crates/c05_threads/src/lockfree/`（无锁数据结构）
   - `crates/c06_async/`（异步编程完整生态）
   - `crates/c04_generic/src/advanced/`（GAT、HRTB）
3. 完成 `exercises/` 下的对应练习题验证掌握度
4. 阅读 `docs/05_guides/BEST_PRACTICES.md` 了解生产实践

### 如果用本项目替代 Google 课程

1. 按 `knowledge/01_fundamentals/` → `02_intermediate/` → `03_advanced/` 顺序学习
2. 每学完一个模块，完成对应的 `exercises/` 练习题
3. 对照本映射文档确认覆盖了 Google 课程的所有内容
4. 运行 `cargo test --workspace` 验证代码理解

---

## 相关文档

- [LFRS_CERTIFICATION_MAPPING.md](./LFRS_CERTIFICATION_MAPPING.md) - LFRS 认证映射
- [PRAGMATIC_GUIDELINES_CHECKLIST.md](../05_guides/PRAGMATIC_GUIDELINES_CHECKLIST.md) - 代码审查清单
- [exercises/README.md](../../exercises/README.md) - 练习题总入口
