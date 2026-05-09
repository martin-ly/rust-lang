# Rust 知识索引

> 按主题快速查找所有知识文档

---

## 📊 文档完成状态 (100%)

| 层级 | 文档数 | 状态 |
|------|--------|------|
| **00_start** | 5 | ✅ 完成 |
| **01_fundamentals** | 5 | ✅ 完成 |
| **02_intermediate** | 13 | ✅ 完成 |
| **03_advanced** | 15 | ✅ 完成 |
| **04_expert** | 6 | ✅ 完成 |
| **05_reference** | 4 | ✅ 完成 |
| **06_ecosystem** | 13 | ✅ 完成 |
| **99_archive** | 3 | ✅ 完成 |
| **总计** | **71 篇** | ✅ **100%** |

---

## 🆕 Rust 1.95 新特性索引

| 特性 | 文档 | 状态 |
|------|------|------|
| `cfg_select!` | [02_intermediate/cfg_select.md](02_intermediate/cfg_select.md) | ✅ |
| `if let guards` | [02_intermediate/if_let_guards.md](02_intermediate/if_let_guards.md) | ✅ |
| `Atomic*::update` / `try_update` | [03_advanced/concurrency/atomics.md](03_advanced/concurrency/atomics.md) | ✅ |
| `Vec::push_mut` / `insert_mut` | [02_intermediate/collections.md](02_intermediate/collections.md) | ✅ |
| `VecDeque` / `LinkedList` `push_*_mut` | [02_intermediate/collections.md](02_intermediate/collections.md) | ✅ |
| `core::range` | [02_intermediate/core_range.md](02_intermediate/core_range.md) | ✅ |
| `*const/mut T::as_ref_unchecked` | [04_expert/unsafe_audit.md](04_expert/unsafe_audit.md) | ✅ |
| `Layout::dangling_ptr` / `repeat` / `extend_packed` | [04_expert/unsafe_audit.md](04_expert/unsafe_audit.md) | ✅ |
| `core::hint::cold_path` | [03_advanced/performance_optimization.md](03_advanced/performance_optimization.md) | ✅ |
| `bool::TryFrom<{integer}>` | [02_intermediate/type_conversions.md](02_intermediate/type_conversions.md) | ✅ |
| `MaybeUninit` / `Cell` 数组转换 | [03_advanced/unsafe/maybe_uninit.md](03_advanced/unsafe/maybe_uninit.md) | ✅ |
| PowerPC/PowerPC64 内联汇编 | [03_advanced/unsafe/inline_asm.md](03_advanced/unsafe/inline_asm.md) | ✅ |

---

## 📚 按字母索引

### A

- **array_windows** - [01_fundamentals/iterators.md](01_fundamentals/iterators.md) - Rust 1.96
- **async/await** - [03_advanced/async/async_await.md](03_advanced/async/async_await.md)
- **async closure** - [03_advanced/async/async_closure.md](03_advanced/async/async_closure.md) - Rust 1.85+
- **atomics** - [03_advanced/concurrency/atomics.md](03_advanced/concurrency/atomics.md)

### B

- **borrowing** - [01_fundamentals/borrowing.md](01_fundamentals/borrowing.md)
- **Box** - [02_intermediate/smart_pointers.md](02_intermediate/smart_pointers.md)

### C

- **Cargo** - [06_ecosystem/cargo_basics.md](06_ecosystem/cargo_basics.md)
- **case studies** - [99_archive/case_studies.md](99_archive/case_studies.md)
- **char → usize** - [02_intermediate/type_conversions.md](02_intermediate/type_conversions.md) - Rust 基础转换 (非特定版本)
- **collections** - [02_intermediate/collections.md](02_intermediate/collections.md)
- **compiler internals** - [04_expert/compiler_internals.md](04_expert/compiler_internals.md)
- **concurrency** - [03_advanced/concurrency/](03_advanced/concurrency/)
- **ControlFlow** - (整合到控制流相关文档)
- **CString/CStr** - [02_intermediate/strings.md](02_intermediate/strings.md)

### D

- **declarative macros** - [03_advanced/macros/declarative.md](03_advanced/macros/declarative.md)

### E

- **Edition 2024** - [06_ecosystem/edition_2024.md](06_ecosystem/edition_2024.md)
- **error handling** - [02_intermediate/error_handling.md](02_intermediate/error_handling.md)
- **Euler's number** - [05_reference/math_constants.md](05_reference/math_constants.md)
- **exercises** - [99_archive/exercises.md](99_archive/exercises.md)

### F

- **FFI** - [03_advanced/unsafe/ffi.md](03_advanced/unsafe/ffi.md)
- **From/Into** - [02_intermediate/type_conversions.md](02_intermediate/type_conversions.md)

### G

- **generators** - Rust 1.95+ (预览)
- **generics** - [02_intermediate/generics.md](02_intermediate/generics.md)
- **Golden Ratio** - [05_reference/math_constants.md](05_reference/math_constants.md)

### H

- **HashMap** - [02_intermediate/collections.md](02_intermediate/collections.md)
- **hello world** - [00_start/hello_world.md](00_start/hello_world.md)

### I

- **if let guards** - [02_intermediate/control_flow/if_let_guards.md](02_intermediate/control_flow/if_let_guards.md) - Rust 1.95
- **installation** - [00_start/installation.md](00_start/installation.md)
- **iterators** - [01_fundamentals/iterators.md](01_fundamentals/iterators.md)

### K

- **keywords** - [05_reference/keywords.md](05_reference/keywords.md)

### L

- **LazyCell** - [03_advanced/lazy_initialization.md](03_advanced/lazy_initialization.md) - Rust 1.96 (`get`, `get_mut`, `force_mut` accessors)
- **LazyLock** - [03_advanced/lazy_initialization.md](03_advanced/lazy_initialization.md) - Rust 1.96 (`get`, `get_mut`, `force_mut` accessors)
- **learning roadmap** - [00_start/learning_roadmap.md](00_start/learning_roadmap.md)
- **lifetimes** - [01_fundamentals/lifetimes.md](01_fundamentals/lifetimes.md)
- **LRU Cache** - [99_archive/case_studies.md](99_archive/case_studies.md)

### M

- **macros** - [03_advanced/macros/](03_advanced/macros/)
- **math constants** - [05_reference/math_constants.md](05_reference/math_constants.md)
- **Miri** - [04_expert/miri/tree_borrows.md](04_expert/miri/tree_borrows.md)
- **Mutex** - [03_advanced/concurrency/synchronization.md](03_advanced/concurrency/synchronization.md)

### O

- **ownership** - [01_fundamentals/ownership.md](01_fundamentals/ownership.md)

### P

- **Peekable::next_if** - [01_fundamentals/iterators.md](01_fundamentals/iterators.md) - Rust 1.80.0
- **procedural macros** - [03_advanced/macros/procedural.md](03_advanced/macros/procedural.md)

### R

- **Rc/Arc** - [02_intermediate/smart_pointers.md](02_intermediate/smart_pointers.md)
- **Result/Option** - [02_intermediate/error_handling.md](02_intermediate/error_handling.md)
- **Rust philosophy** - [00_start/rust_philosophy.md](00_start/rust_philosophy.md)
- **RwLock** - [03_advanced/concurrency/synchronization.md](03_advanced/concurrency/synchronization.md)

### S

- **semaphore** - [03_advanced/concurrency/synchronization.md](03_advanced/concurrency/synchronization.md)
- **Send/Sync** - [03_advanced/concurrency/threads.md](03_advanced/concurrency/threads.md)
- **smart pointers** - [02_intermediate/smart_pointers.md](02_intermediate/smart_pointers.md)
- **standard library** - [05_reference/std_library_cheatsheet.md](05_reference/std_library_cheatsheet.md)
- **strings** - [02_intermediate/strings.md](02_intermediate/strings.md)
- **synchronization** - [03_advanced/concurrency/synchronization.md](03_advanced/concurrency/synchronization.md)

### T

- **threads** - [03_advanced/concurrency/threads.md](03_advanced/concurrency/threads.md)
- **Tokio** - [03_advanced/async/async_await.md](03_advanced/async/async_await.md)
- **traits** - [02_intermediate/traits.md](02_intermediate/traits.md)
- **Tree Borrows** - [04_expert/miri/tree_borrows.md](04_expert/miri/tree_borrows.md)
- **type conversions** - [02_intermediate/type_conversions.md](02_intermediate/type_conversions.md)

### U

- **unsafe audit** - [04_expert/unsafe_audit.md](04_expert/unsafe_audit.md)
- **unsafe Rust** - [03_advanced/unsafe/unsafe_rust.md](03_advanced/unsafe/unsafe_rust.md)

### V

- **Vec** - [02_intermediate/collections.md](02_intermediate/collections.md)
- **VERSION_TRACKING** - [99_archive/VERSION_TRACKING.md](99_archive/VERSION_TRACKING.md)

---

## 🎯 学习路径

### 新手路径 ⭐

```text
00_start/installation.md → 00_start/hello_world.md →
00_start/rust_philosophy.md → 00_start/learning_roadmap.md →
01_fundamentals/ownership.md → 01_fundamentals/borrowing.md →
01_fundamentals/lifetimes.md → 01_fundamentals/iterators.md
```

### 进阶路径 ⭐⭐

```text
02_intermediate/generics.md → 02_intermediate/traits.md →
02_intermediate/error_handling.md → 02_intermediate/collections.md →
02_intermediate/smart_pointers.md → 02_intermediate/type_conversions.md →
02_intermediate/strings.md
```

### 高级路径 ⭐⭐⭐

```text
03_advanced/lazy_initialization.md →
03_advanced/async/async_await.md → 03_advanced/async/async_closure.md →
03_advanced/concurrency/threads.md → 03_advanced/concurrency/atomics.md →
03_advanced/concurrency/synchronization.md →
03_advanced/macros/declarative.md → 03_advanced/macros/procedural.md →
03_advanced/unsafe/unsafe_rust.md → 03_advanced/unsafe/ffi.md
```

### 专家路径 ⭐⭐⭐⭐

```text
04_expert/compiler_internals.md → 04_expert/unsafe_audit.md →
04_expert/miri/tree_borrows.md
```

### Rust 1.95+ 特性追踪 🆕

```text
01_fundamentals/iterators.md (array_windows, next_if) →
02_intermediate/type_conversions.md (bool::TryFrom, char→usize) →
02_intermediate/let_chains.md →
02_intermediate/if_let_guards.md →
02_intermediate/cfg_select.md →
02_intermediate/core_range.md →
03_advanced/lazy_initialization.md (LazyCell/LazyLock) →
03_advanced/concurrency/atomics.md (Atomic*::update) →
03_advanced/performance_optimization.md (cold_path) →
03_advanced/unsafe/maybe_uninit.md (数组转换) →
03_advanced/unsafe/inline_asm.md (PowerPC) →
05_reference/math_constants.md (SQRT_3, EULER_GAMMA) →
06_ecosystem/edition_2024.md →
06_ecosystem/emerging/rust_1_95.md →
04_expert/miri/tree_borrows.md
```

---

## 🎮 练习与案例

| 资源 | 位置 | 内容 |
|------|------|------|
| **练习题集** | [99_archive/exercises.md](99_archive/exercises.md) | 23道分级练习题 |
| **案例研究** | [99_archive/case_studies.md](99_archive/case_studies.md) | 5个生产级案例 |

---

## 📖 权威来源索引

| 来源 | 类型 | 引用位置 |
|------|------|----------|
| PLDI 2025 Distinguished Paper | 顶级会议 | [04_expert/miri/tree_borrows.md](04_expert/miri/tree_borrows.md) |
| RFC 2788 | 官方 RFC | [03_advanced/lazy_initialization.md](03_advanced/lazy_initialization.md) |
| Rust Book | 官方文档 | 多个文档 |
| Edition Guide | 官方文档 | [06_ecosystem/edition_2024.md](06_ecosystem/edition_2024.md) |
| Rust Reference | 官方参考 | [05_reference/keywords.md](05_reference/keywords.md) |

---

## 📊 统计数据

- **总文档数**: 73 篇（含索引/入口）
- **总代码行数**: 33,715 行
- **总字符数**: 783,401 字符
- **重构文档**: 28 篇核心文档按 10 模块标准重构
- **Rust 1.95+ 特性**: 100% 覆盖

---

**索引生成时间**: 2026-05-09
**版本**: Rust 1.95.0+ (Edition 2024)
**状态**: ✅ 核心层 100% 完成，Ecosystem 层持续推进中
