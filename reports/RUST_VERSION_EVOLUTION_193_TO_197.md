# Rust 版本演进全景报告（1.93 → 1.97）

> **生成日期**: 2026-05-11
> **工具链**: rustc 1.97.0-nightly (2026-05-05), Edition 2024
> **项目**: rust-lang 系统学习 workspace（15 crates + exercises + proc-macro）

---

## 1. 版本全景矩阵

| 特性类别 | 1.93 | 1.94 | 1.95 | 1.96 | 1.97 |
|---------|------|------|------|------|------|
| **生成器** | - | - | gen blocks | - | - |
| **异步** | - | - | AsyncFn traits | - | - |
| **模式匹配** | - | let chains | if let guards | - | - |
| **Unsafe** | addr_of! | - | raw const | - | - |
| **Unsafe** | - | - | unsafe_op_in_unsafe_fn | - | - |
| **FFI** | - | - | c"..." | - | - |
| **Const** | const {} 部分 | - | const {} 扩展 | - | - |
| **迭代器** | - | array_windows | - | - | repeat_n |
| **集合** | into_raw_parts | - | - | VecDeque::resize | Vec::pop_if |
| **Pin** | - | - | - | - | pin! macro |
| **Option/Result** | - | - | - | - | is_none_or |
| **IO** | - | - | - | - | io::Error::other |
| **LTO** | - | - | linker-plugin-lto | - | - |

---

## 2. Rust 1.93 — 内存与集合增强

| 特性 | 说明 | 本项目覆盖 |
|------|------|-----------|
| String/Vec into_raw_parts | 分解为 (ptr, len, cap) | 14 crates |
| MaybeUninit 切片方法 | assume_init_ref, assume_init_mut, assume_init_drop | c01, c05, c13 |
| slice::as_array / as_mut_array | &[T] -> Option<&[T; N]> | c02, c04, c08 |
| char::MAX_LEN_UTF8 / MAX_LEN_UTF16 | 字符编码常量 | c02, c10, c13 |
| std::fmt::from_fn | 从闭包创建 impl Display | c03, c09, c11 |
| VecDeque::pop_front_if / pop_back_if | 条件弹出 | c03, c08 |

---

## 3. Rust 1.94 — 控制流与迭代器

| 特性 | 说明 | 本项目覆盖 |
|------|------|-----------|
| array_windows | 固定大小滑动窗口迭代 | c01, c08 |
| let chains | if let A = a && let B = b | c03 |
| ControlFlow::map / map_err | 控制流映射 | c02, c03, c08, c09 |
| Peekable::next_if_map | 条件提取 | c08 |

---

## 4. Rust 1.95 — 核心语言里程碑（主焦点）

### 4.1 gen blocks — 原生生成器

本项目实践:

- exercises: 6 个专项练习（斐波那契、过滤映射、扁平化、K-way合并、去重、滑动窗口）
- c04_generic: 3 个生产重构（Counter、NumberIterator x2）
- c08_algorithms: 4 个生产算法（even_numbers、merge_sorted、dedup_sorted、window_sum）

### 4.2 AsyncFn trait 家族 — 异步闭包类型化

本项目实践: c04_generic（泛型 trait bound）、c06_async（异步映射）、c09_design_pattern（策略模式）

### 4.3 raw const / raw mut — 原始引用操作符

本项目实践:

- c05_threads lock-free: hazard_pointers.rs 中 HP 注册/注销重构
- exercises ex08: packed struct + union 安全访问练习（7 测试）
- exercises ex11: const fn 中的 raw const

### 4.4 unsafe_op_in_unsafe_fn — Rust 2024 unsafe 语义

本项目实践: exercises ex09（完整 RawBuffer 内存管理 + 4 道判断题）

### 4.5 c"..." C 字符串字面量

本项目实践: exercises ex10（7 个测试）、c07/c10/c11/c12/c13

### 4.6 1.95 特性覆盖统计

| 模块 | 测试数 | 难度分布 |
|------|--------|---------|
| exercises unsafe_rust | 66 (Miri 通过) | Easy-Hard |
| exercises 195/196 feature | 21 | Medium |
| 15 crates rust_195_features | ~40 | Easy-Medium |

---

## 5. Rust 1.96 — 标准库完善

| 特性 | 说明 | 本项目覆盖 |
|------|------|-----------|
| VecDeque::resize | 调整双端队列大小 | 15 crates |
| std::iter::repeat_n | 有限次重复迭代器 | c11_proc, common, c13 |

---

## 6. Rust 1.97 — 类型系统与工具链

| 特性 | 说明 | 本项目覆盖 |
|------|------|-----------|
| std::pin::pin!() | 栈上固定宏，避免堆分配 | c01, c05, c06, c12 |
| Option::is_none_or | None || predicate 语义 | c02, c03, c09, c11_proc, common |
| Result::is_ok_and | Ok && predicate 语义 | c02, c03, c09, common |
| Vec::pop_if | 条件弹出 | c01, c04, c05, c08, c11, c12 |
| io::Error::other | 快速创建 IO 错误 | c07, c10, c13 |

---

## 7. 本项目覆盖统计

### 7.1 文件规模

| 版本文件 | 覆盖 crate 数 | 总代码行数 | 测试数 |
|---------|--------------|-----------|--------|
| rust_193_features.rs | 15 | ~1,800 | ~60 |
| rust_195_features.rs | 15 | ~2,500 | ~80 |
| rust_196_features.rs | 15 | ~1,200 | ~45 |
| rust_197_features.rs | 15 | ~1,500 | ~55 |
| exercises 195/196 | 1 | ~800 | 21 |
| exercises unsafe_rust | 1 | ~2,000 | 66 |

### 7.2 特性覆盖完整度

| 版本 | 可用特性数 | 本项目覆盖数 | 覆盖率 |
|------|-----------|-------------|--------|
| 1.93 | 7 | 7 | 100% |
| 1.94 | 4 | 4 | 100% |
| 1.95 | 9 | 8 | 89% (Box::into_raw in const fn 不可用) |
| 1.96 | 2 | 2 | 100% |
| 1.97 | 5 | 5 | 100% |

---

## 8. Miri 安全验证结论

| 模块 | 测试数 | 结果 |
|------|--------|------|
| c05_threads lock-free | 12 passed, 4 ignored | 零 UB |
| exercises unsafe_rust | 66 passed, 1 ignored | 零 UB |
| raw const 专项 | 7 passed | 零违规 |

---

## 9. 版本文件映射

| Crate | 193 | 195 | 196 | 197 |
|-------|-----|-----|-----|-----|
| c01_ownership_borrow_scope | Yes | Yes | Yes | Yes |
| c02_type_system | Yes | Yes | Yes | Yes |
| c03_control_fn | Yes | Yes | Yes | Yes |
| c04_generic | Yes | Yes | Yes | Yes |
| c05_threads | Yes | Yes | Yes | Yes |
| c06_async | Yes | Yes | Yes | Yes |
| c07_process | Yes | Yes | Yes | Yes |
| c08_algorithms | Yes | Yes | Yes | Yes |
| c09_design_pattern | Yes | Yes | Yes | Yes |
| c10_networks | Yes | Yes | Yes | Yes |
| c11_macro_system | Yes | Yes | Yes | Yes |
| c11_macro_system_proc | Yes | Yes | Yes | Yes |
| c12_wasm | Yes (archive) | Yes | Yes | Yes |
| c13_embedded | Yes | Yes | Yes | Yes |
| common | Yes | Yes | Yes | Yes |
| exercises | - | Yes | Yes | - |

---

## 结论

本项目已建立从 1.93 到 1.97 的完整版本追踪体系:

- 15 个 crate 每个都有 4 个版本特性文件
- exercises 包含 66 道 unsafe_rust 练习 + 21 道版本特性练习
- 3 份系统报告覆盖解析、验证、演进三个维度
- Miri 验证确认所有单线程 unsafe 路径零 UB

下一步建议:

1. 前瞻 Rust 1.98 特性（如 impl Trait in type aliases 稳定化、gen blocks 去 feature gate）
2. 将 gen blocks 稳定化后的生产级重构（一旦 nightly 移除 feature gate）
3. 构建跨版本特性对比的交互式文档
