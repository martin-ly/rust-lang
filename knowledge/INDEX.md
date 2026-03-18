# Rust 知识索引

> 按主题快速查找所有知识文档

---

## 📊 文档完成状态

| 层级 | 文档 | 状态 |
|------|------|------|
| **00_start** | 4篇 | ✅ 完成 |
| **01_fundamentals** | iterators.md (含 1.94 特性) | ✅ 完成 |
| **02_intermediate** | 5篇 | ✅ 完成 |
| **03_advanced** | lazy_initialization.md + async/并发 | ✅ 完成 |
| **04_expert** | miri/tree_borrows.md | ✅ 完成 |
| **05_reference** | math_constants.md | ✅ 完成 |
| **06_ecosystem** | edition_2024.md, cargo_basics.md | ✅ 完成 |

---

## 🆕 Rust 1.94 新特性索引

| 特性 | 文档 | 重要程度 | 状态 |
|------|------|----------|------|
| `array_windows` | [01_fundamentals/iterators.md](01_fundamentals/iterators.md) | ⭐⭐⭐⭐⭐ | ✅ 已更新 |
| `LazyCell/LazyLock` | [03_advanced/lazy_initialization.md](03_advanced/lazy_initialization.md) | ⭐⭐⭐⭐⭐ | ✅ 已更新 |
| `char` → `usize` | (整合到 02_intermediate/type_conversions.md) | ⭐⭐⭐ | ✅ 已更新 |
| 数学常量 | [05_reference/math_constants.md](05_reference/math_constants.md) | ⭐⭐⭐ | ✅ 已更新 |
| `ControlFlow` | (整合到 03_advanced/control_flow.md) | ⭐⭐⭐⭐ | ✅ 已更新 |
| `Peekable::next_if` | [01_fundamentals/iterators.md](01_fundamentals/iterators.md) | ⭐⭐⭐ | ✅ 已更新 |
| Edition 2024 | [06_ecosystem/edition_2024.md](06_ecosystem/edition_2024.md) | ⭐⭐⭐⭐⭐ | ✅ 已更新 |
| Miri Tree Borrows | [04_expert/miri/tree_borrows.md](04_expert/miri/tree_borrows.md) | ⭐⭐⭐⭐⭐ | ✅ 已更新 |

---

## 📚 按字母索引

### A

- **array_windows** - [01_fundamentals/iterators.md](01_fundamentals/iterators.md) - Rust 1.94 新特性
- **async/await** - [03_advanced/async/async_await.md](03_advanced/async/async_await.md)

### B

- **borrowing** - [01_fundamentals/borrowing.md](01_fundamentals/borrowing.md) (待创建)

### C

- **Cargo** - [06_ecosystem/cargo_basics.md](06_ecosystem/cargo_basics.md)
- **char → usize** - Rust 1.94 类型转换
- **collections** - [02_intermediate/collections.md](02_intermediate/collections.md)

### E

- **Edition 2024** - [06_ecosystem/edition_2024.md](06_ecosystem/edition_2024.md)
- **error handling** - [02_intermediate/error_handling.md](02_intermediate/error_handling.md)
- **Euler's Gamma** - [05_reference/math_constants.md](05_reference/math_constants.md)

### G

- **generators** - Rust 1.95 预览
- **generics** - [02_intermediate/generics.md](02_intermediate/generics.md)
- **Golden Ratio** - [05_reference/math_constants.md](05_reference/math_constants.md)

### I

- **installation** - [00_start/installation.md](00_start/installation.md)
- **iterators** - [01_fundamentals/iterators.md](01_fundamentals/iterators.md)

### L

- **LazyCell** - [03_advanced/lazy_initialization.md](03_advanced/lazy_initialization.md) - Rust 1.94
- **LazyLock** - [03_advanced/lazy_initialization.md](03_advanced/lazy_initialization.md) - Rust 1.94
- **learning roadmap** - [00_start/learning_roadmap.md](00_start/learning_roadmap.md)
- **lifetimes** - [01_fundamentals/lifetimes.md](01_fundamentals/lifetimes.md) (待创建)

### M

- **math constants** - [05_reference/math_constants.md](05_reference/math_constants.md)
- **Miri** - [04_expert/miri/tree_borrows.md](04_expert/miri/tree_borrows.md)

### O

- **ownership** - [01_fundamentals/ownership.md](01_fundamentals/ownership.md) (待创建)

### P

- **Peekable::next_if** - [01_fundamentals/iterators.md](01_fundamentals/iterators.md) - Rust 1.94

### R

- **Result/Option** - [02_intermediate/error_handling.md](02_intermediate/error_handling.md)

### S

- **smart pointers** - [02_intermediate/smart_pointers.md](02_intermediate/smart_pointers.md)

### T

- **threads** - [03_advanced/concurrency/threads.md](03_advanced/concurrency/threads.md)
- **traits** - [02_intermediate/traits.md](02_intermediate/traits.md)
- **Tree Borrows** - [04_expert/miri/tree_borrows.md](04_expert/miri/tree_borrows.md) - PLDI 2025

---

## 🎯 学习路径

### 新手路径

```
00_start/installation.md → 00_start/hello_world.md →
00_start/rust_philosophy.md → 00_start/learning_roadmap.md →
01_fundamentals/iterators.md → ...
```

### 特性追踪

```
01_fundamentals/iterators.md (array_windows, next_if) →
03_advanced/lazy_initialization.md (LazyCell/LazyLock) →
06_ecosystem/edition_2024.md →
04_expert/miri/tree_borrows.md
```

---

## 📖 权威来源索引

| 来源 | 类型 | 引用位置 |
|------|------|----------|
| PLDI 2025 Distinguished Paper | 顶级会议 | [04_expert/miri/tree_borrows.md](04_expert/miri/tree_borrows.md) |
| RFC 2788 | 官方 RFC | [03_advanced/lazy_initialization.md](03_advanced/lazy_initialization.md) |
| Edition Guide | 官方文档 | [06_ecosystem/edition_2024.md](06_ecosystem/edition_2024.md) |
| Rust Book | 官方文档 | 多个文档 |

---

**索引生成时间**: 2026-03-19
**版本**: Rust 1.94.0
**总文档数**: 20+ 篇
