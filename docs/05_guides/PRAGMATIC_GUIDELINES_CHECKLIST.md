# Microsoft Pragmatic Rust Guidelines 代码审查清单

> **创建日期**: 2026-04-24  
> **来源**: Microsoft Pragmatic Rust Guidelines  
> **用途**: 将指南要点转化为可执行的代码审查清单，每条附带项目内示例链接

---

## 清单使用说明

在代码审查（Code Review）或自我检查时使用此清单。每条指南标注：

- **必须 (MUST)**: 违反会导致 bugs 或安全问题
- **应该 (SHOULD)**: 违反会降低代码质量
- **建议 (MAY)**: 可选的最佳实践

---

## 1. 安全 (Safety)

### 1.1 Unsafe 代码管理

| # | 指南 | 级别 | 项目示例 | 检查项 |
| :--- | :--- | :--- | :--- | :--- |
| S01 | 最小化 unsafe 代码块范围 | MUST | `docs/03_guides/UNSAFE_RUST_GUIDE.md` | unsafe 块是否包含最小必要代码？ |
| S02 | 每个 unsafe 块必须有 SAFETY 注释 | MUST | `crates/c13_embedded/src/` | 是否包含 `// SAFETY: ...` 说明？ |
| S03 | 优先使用 safe 抽象封装 unsafe | MUST | `crates/c01_ownership_borrow_scope/src/internal_mut/` | unsafe 是否被封装在安全 API 后？ |
| S04 | 避免不必要的 `unsafe_code` 允许 | SHOULD | `Cargo.toml` `[workspace.lints.rust]` | 是否保持 `unsafe_code = "forbid"`？ |
| S05 | 使用 Miri 验证 unsafe 代码 | SHOULD | `docs/03_guides/MIRI_GUIDE.md` | 关键 unsafe 代码是否通过 Miri？ |

### 1.2 输入验证

| # | 指南 | 级别 | 项目示例 | 检查项 |
| :--- | :--- | :--- | :--- | :--- |
| S06 | 公共 API 必须验证输入边界 | MUST | `exercises/src/error_handling/ex02_custom_error.rs` | 函数参数是否有范围检查？ |
| S07 | 避免使用 `unwrap()` / `expect()` 在库代码中 | MUST | `crates/*/src/lib.rs` | 生产代码是否使用 `?` 替代 `unwrap`？ |
| S08 | 索引操作前必须验证边界 | MUST | `crates/c08_algorithms/src/` | 所有 `[i]` 索引是否有前置检查？ |
| S09 | 字符串解析必须处理错误 | MUST | `exercises/src/error_handling/ex01_result_option.rs` | `parse()` 是否处理了 Err？ |

### 1.3 并发安全

| # | 指南 | 级别 | 项目示例 | 检查项 |
| :--- | :--- | :--- | :--- | :--- |
| S10 | 共享可变状态必须使用同步原语 | MUST | `crates/c05_threads/src/synchronization/` | `Mutex`/`RwLock` 是否包裹了共享数据？ |
| S11 | 避免在持有锁时执行阻塞操作 | MUST | `crates/c05_threads/src/synchronization/mutex/` | lock() 后是否有 I/O 或睡眠？ |
| S12 | 优先使用消息传递而非共享状态 | SHOULD | `crates/c05_threads/src/message_passing/` | 是否可以考虑 channel 替代 Mutex？ |
| S13 | async 中避免持有同步锁跨越 await | MUST | `crates/c06_async/src/await/` | `await` 前是否已释放 MutexGuard？ |

---

## 2. 性能 (Performance)

### 2.1 内存分配

| # | 指南 | 级别 | 项目示例 | 检查项 |
| :--- | :--- | :--- | :--- | :--- |
| P01 | 避免在热路径上分配内存 | SHOULD | `crates/c08_algorithms/src/performance_optimization.rs` | 循环内是否有 `String::new()` / `vec![]`？ |
| P02 | 使用 `with_capacity` 预分配 Vec | SHOULD | `exercises/src/concurrency/ex03_channel_mpsc.rs` | `Vec::new()` 是否可替换为 `with_capacity`？ |
| P03 | 优先使用 &str 而非 String 作为参数 | SHOULD | `exercises/src/ownership_borrowing/ex02_string_slice.rs` | 函数参数是否为 `&str` 而非 `String`？ |
| P04 | 避免不必要的 clone | SHOULD | `crates/c01_ownership_borrow_scope/src/copy_move/` | clone() 是否可以通过借用消除？ |
| P05 | 使用 Cow<'_, str> 处理可选克隆 | MAY | `docs/02_reference/quick_reference/ownership_cheatsheet.md` | 读多写少场景是否使用了 Cow？ |

### 2.2 迭代与集合

| # | 指南 | 级别 | 项目示例 | 检查项 |
| :--- | :--- | :--- | :--- | :--- |
| P06 | 优先使用迭代器而非显式循环 | SHOULD | `exercises/src/type_system/ex04_generics_intro.rs` | `for` 循环是否可以用 `map/filter` 替代？ |
| P07 | 避免在迭代中重复查找 | SHOULD | `crates/c02_type_system/src/type_composition/collection/hash_map.rs` | 是否多次查询同一个 HashMap 键？ |
| P08 | 使用 Entry API 进行条件插入 | SHOULD | `crates/c02_type_system/src/type_composition/collection/hash_map.rs` | `contains_key` + `insert` 是否可用 `entry` 替代？ |
| P09 | 大结构体使用 Box 减少栈压力 | MAY | `crates/c01_ownership_borrow_scope/src/ownership/` | 递归类型或大结构体是否使用了 Box？ |

### 2.3 并发性能

| # | 指南 | 级别 | 项目示例 | 检查项 |
| :--- | :--- | :--- | :--- | :--- |
| P10 | 区分 CPU 密集与 I/O 密集任务 | MUST | `crates/c05_threads/src/threads/thread_pool/` | 线程池配置是否匹配任务类型？ |
| P11 | 无锁场景优先使用 Atomic | SHOULD | `exercises/src/concurrency/ex05_arc_atomic.rs` | 简单计数器是否使用了 Atomic 而非 Mutex？ |
| P12 | 批量发送消息减少同步开销 | SHOULD | `crates/c05_threads/src/message_passing/mpsc/` | channel 是否是逐条发送而非批量？ |

---

## 3. 可读性 (Readability)

### 3.1 命名规范

| # | 指南 | 级别 | 项目示例 | 检查项 |
| :--- | :--- | :--- | :--- | :--- |
| R01 | 类型使用 PascalCase | MUST | 所有 `struct`/`enum` 定义 | 结构体/枚举名是否大写开头？ |
| R02 | 函数与变量使用 snake_case | MUST | 所有 `fn` 定义 | 函数名是否小写+下划线？ |
| R03 | 常量使用 SCREAMING_SNAKE_CASE | MUST | `crates/*/src/lib.rs` | `const`/`static` 是否全大写？ |
| R04 | 避免单字母命名（迭代器除外） | SHOULD | `exercises/src/` | 变量名是否有描述性？ |
| R05 | 布尔变量使用 `is_` / `has_` / `can_` 前缀 | SHOULD | `exercises/src/generics_traits/ex04_default_trait.rs` | `enable_logging` vs `logging`？ |
| R06 | Result/Option 变量使用描述性名称 | SHOULD | `exercises/src/error_handling/ex03_error_propagation.rs` | `let content = fs::read_to_string(...)`？ |

### 3.2 代码组织

| # | 指南 | 级别 | 项目示例 | 检查项 |
| :--- | :--- | :--- | :--- | :--- |
| R07 | 函数长度不超过 50 行 | SHOULD | 所有 crate 源码 | 是否有需要拆分的过长函数？ |
| R08 | 模块职责单一 | SHOULD | `crates/c02_type_system/src/` | 每个 mod.rs 是否只做一件事？ |
| R09 | 使用 `use` 组织导入，避免通配符 | SHOULD | 所有 `use` 语句 | 是否有 `use module::*`？ |
| R10 | 相关代码垂直靠近 | SHOULD | `crates/c04_generic/src/trait_bound/` | 结构体定义是否靠近其 impl？ |
| R11 | 优先使用方法链而非嵌套调用 | MAY | `exercises/src/type_system/ex04_generics_intro.rs` | `a.b().c().d()` vs `d(c(b(a)))`？ |

### 3.3 注释与文档

| # | 指南 | 级别 | 项目示例 | 检查项 |
| :--- | :--- | :--- | :--- | :--- |
| R12 | 公共 API 必须有文档注释 | MUST | `exercises/src/*/ex*.rs` | `pub fn` 是否有 `///` 文档？ |
| R13 | 复杂算法必须解释 "为什么" | SHOULD | `crates/c08_algorithms/src/` | 是否有非显而易见的代码缺少注释？ |
| R14 | 避免注释与代码重复 | SHOULD | 全部代码 | 注释是否解释了意图而非重复代码？ |
| R15 | 使用 TODO/FIXME 标记临时代码 | MAY | `exercises/src/unsafe_rust/mod.rs` | 是否有未标记的临时实现？ |

---

## 4. API 设计

### 4.1 类型设计

| # | 指南 | 级别 | 项目示例 | 检查项 |
| :--- | :--- | :--- | :--- | :--- |
| A01 | 使用类型系统表达约束（Make Illegal States Unrepresentable） | MUST | `exercises/src/type_system/ex01_enum_pattern_match.rs` | 是否用 enum 替代了 magic number？ |
| A02 | 优先使用 &str / &[T] 作为输入 | SHOULD | `exercises/src/ownership_borrowing/ex02_string_slice.rs` | API 是否接收引用而非所有权？ |
| A03 | 返回 Result 而非 panic | MUST | `exercises/src/error_handling/ex03_error_propagation.rs` | 错误情况是否返回 Err？ |
| A04 | 使用 Builder 模式构造复杂对象 | MAY | `crates/c09_design_pattern/` | 多参数构造是否有 Builder？ |
| A05 | 实现 Default 减少构造函数参数 | SHOULD | `exercises/src/generics_traits/ex04_default_trait.rs` | 复杂结构体是否实现了 Default？ |

### 4.2 错误设计

| # | 指南 | 级别 | 项目示例 | 检查项 |
| :--- | :--- | :--- | :--- | :--- |
| A06 | 错误类型实现 std::error::Error | MUST | `exercises/src/error_handling/ex02_custom_error.rs` | 自定义错误是否实现了 Error trait？ |
| A07 | 错误信息包含上下文 | SHOULD | `exercises/src/error_handling/ex03_error_propagation.rs` | `map_err` 是否添加了上下文？ |
| A08 | 使用 thiserror/anyhow 减少样板 | MAY | `Cargo.toml` workspace deps | 是否使用了生态库简化错误处理？ |

### 4.3 Trait 设计

| # | 指南 | 级别 | 项目示例 | 检查项 |
| :--- | :--- | :--- | :--- | :--- |
| A09 | Trait 方法数量适中（<= 5 个优先） | SHOULD | `exercises/src/type_system/ex05_trait_object.rs` | Trait 是否过于庞大？ |
| A10 | 关联类型 vs 泛型参数选择恰当 | SHOULD | `exercises/src/generics_traits/ex02_associated_types.rs` | 何时用关联类型、何时用泛型？ |
| A11 | 为常用组合实现 convenience methods | MAY | `crates/c02_type_system/src/type_class/` | 是否有常用的方法组合未提供？ |

---

## 5. 命名规范补充

### 5.1 项目特定约定

| # | 指南 | 级别 | 项目示例 | 检查项 |
| :--- | :--- | :--- | :--- | :--- |
| N01 | Crate 命名使用 `cNN_` 前缀 | MUST | `Cargo.toml` members | 模块 crate 是否使用 `c01_` 格式？ |
| N02 | 示例文件使用 `_exp.rs` 后缀 | SHOULD | `crates/*/src/bin/` | bin 示例是否有统一后缀？ |
| N03 | 文档使用中文，代码注释视受众而定 | MUST | `docs/` 所有文件 | 文档是否为中文？ |
| N04 | 测试函数使用 `test_` 前缀 | SHOULD | `exercises/src/*/ex*.rs` | `#[test]` 函数是否以 `test_` 开头？ |
| N05 | 练习编号使用 `exNN_` 格式 | SHOULD | `exercises/src/` | 练习文件是否统一编号？ |

---

## 审查清单速查表

### 提交前自检（开发者）

- [ ] `cargo check` 通过
- [ ] `cargo clippy` 无警告（或所有警告已解释）
- [ ] `cargo test` 全部通过
- [ ] 新增公共 API 有文档注释
- [ ] 无未处理的 `unwrap()` / `expect()`（测试代码除外）
- [ ] unsafe 代码有 SAFETY 注释
- [ ] 无 `todo!()` 遗留（除非明确标记为 WIP）

### 代码审查（审查者）

- [ ] 安全: S01–S13 检查项无风险
- [ ] 性能: P01–P12 无明显瓶颈
- [ ] 可读性: R01–R15 符合团队规范
- [ ] API 设计: A01–A11 接口合理
- [ ] 命名: N01–N05 符合项目约定

---

## 自动化检查

本项目已配置以下自动化检查：

| 工具 | 配置位置 | 检查内容 |
| :--- | :--- | :--- |
| Clippy | `.clippy.toml` + `Cargo.toml` `[workspace.lints.clippy]` | 代码质量、性能、风格 |
| rustfmt | `.rustfmt.toml`（如有） | 代码格式化 |
| cargo-deny | （可选） | 依赖安全与许可证 |
| Miri | `docs/03_guides/MIRI_GUIDE.md` | 未定义行为检测 |
| cargo-tarpaulin | `docs/03_guides/TEST_COVERAGE.md` | 测试覆盖率 |

---

## 相关文档

- [LFRS_CERTIFICATION_MAPPING.md](../01_learning/LFRS_CERTIFICATION_MAPPING.md) - 认证考点映射
- [GOOGLE_RUST_MAPPING.md](../01_learning/GOOGLE_RUST_MAPPING.md) - Google 课程映射
- [BEST_PRACTICES.md](./BEST_PRACTICES.md) - 生产实践指南
- [exercises/README.md](../../exercises/README.md) - 练习题入口
