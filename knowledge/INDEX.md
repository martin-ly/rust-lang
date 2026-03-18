# Rust 知识索引

> 按主题快速查找所有知识文档

---

## A

- **array_windows** - [01_fundamentals/iterators.md](01_fundamentals/iterators.md) - Rust 1.94 新特性
- **async/await** - [03_advanced/async/](03_advanced/async/) - 异步编程完整指南

## B

- **borrowing** - [01_fundamentals/borrowing.md](01_fundamentals/borrowing.md) - 借用系统深度解析
- **Box** - [02_intermediate/smart_pointers.md](02_intermediate/smart_pointers.md)

## C

- **char → usize** - [02_intermediate/type_conversions.md](02_intermediate/type_conversions.md) - Rust 1.94
- **closures** - [02_intermediate/closures.md](02_intermediate/closures.md)
- **concurrency** - [03_advanced/concurrency/](03_advanced/concurrency/)
- **const generics** - [02_intermediate/const_generics.md](02_intermediate/const_generics.md)
- **ControlFlow** - [03_advanced/control_flow.md](03_advanced/control_flow.md) - Rust 1.94
- **crate** - [06_ecosystem/crate_management.md](06_ecosystem/crate_management.md)

## D

- **drop** - [02_intermediate/drop.md](02_intermediate/drop.md)
- **dyn** - [02_intermediate/trait_objects.md](02_intermediate/trait_objects.md)

## E

- **Edition 2024** - [06_ecosystem/edition_2024.md](06_ecosystem/edition_2024.md)
- **enums** - [01_fundamentals/enums.md](01_fundamentals/enums.md)
- **error handling** - [02_intermediate/error_handling.md](02_intermediate/error_handling.md)

## F

- **ffi** - [03_advanced/ffi.md](03_advanced/ffi.md)
- **functions** - [01_fundamentals/functions.md](01_fundamentals/functions.md)

## G

- **generators** - [03_advanced/generators.md](03_advanced/generators.md) - Rust 1.95 预览
- **generics** - [02_intermediate/generics.md](02_intermediate/generics.md)
- **gen keyword** - [03_advanced/generators.md](03_advanced/generators.md) - Rust 1.95 预览

## I

- **iterators** - [01_fundamentals/iterators.md](01_fundamentals/iterators.md)

## L

- **LazyCell** - [03_advanced/lazy_initialization.md](03_advanced/lazy_initialization.md) - Rust 1.94
- **LazyLock** - [03_advanced/lazy_initialization.md](03_advanced/lazy_initialization.md) - Rust 1.94
- **lifetimes** - [01_fundamentals/lifetimes.md](01_fundamentals/lifetimes.md)
- **loops** - [01_fundamentals/loops.md](01_fundamentals/loops.md)

## M

- **macros** - [03_advanced/macros/](03_advanced/macros/)
- **match** - [01_fundamentals/pattern_matching.md](01_fundamentals/pattern_matching.md)
- **math constants** - [05_reference/math_constants.md](05_reference/math_constants.md) - Rust 1.94
- **memory** - [01_fundamentals/memory_management.md](01_fundamentals/memory_management.md)
- **Miri** - [04_expert/miri/](04_expert/miri/)
- **modules** - [02_intermediate/modules.md](02_intermediate/modules.md)
- **mutability** - [01_fundamentals/mutability.md](01_fundamentals/mutability.md)

## O

- **ownership** - [01_fundamentals/ownership.md](01_fundamentals/ownership.md)
- **Option** - [02_intermediate/option_result.md](02_intermediate/option_result.md)

## P

- **Peekable::next_if** - [01_fundamentals/iterators.md](01_fundamentals/iterators.md) - Rust 1.94
- **pattern matching** - [01_fundamentals/pattern_matching.md](01_fundamentals/pattern_matching.md)
- **Pin** - [03_advanced/pin.md](03_advanced/pin.md)

## R

- **Rc** - [02_intermediate/smart_pointers.md](02_intermediate/smart_pointers.md)
- **Result** - [02_intermediate/option_result.md](02_intermediate/option_result.md)

## S

- **slices** - [01_fundamentals/slices.md](01_fundamentals/slices.md)
- **smart pointers** - [02_intermediate/smart_pointers.md](02_intermediate/smart_pointers.md)
- **strings** - [02_intermediate/strings.md](02_intermediate/strings.md)
- **structs** - [01_fundamentals/structs.md](01_fundamentals/structs.md)

## T

- **threads** - [03_advanced/concurrency/threads.md](03_advanced/concurrency/threads.md)
- **trait objects** - [02_intermediate/trait_objects.md](02_intermediate/trait_objects.md)
- **traits** - [02_intermediate/traits.md](02_intermediate/traits.md)
- **Tree Borrows** - [04_expert/miri/tree_borrows.md](04_expert/miri/tree_borrows.md)
- **tuples** - [01_fundamentals/tuples.md](01_fundamentals/tuples.md)

## U

- **unsafe** - [03_advanced/unsafe/](03_advanced/unsafe/)

## V

- **variables** - [01_fundamentals/variables.md](01_fundamentals/variables.md)
- **vectors** - [02_intermediate/vectors.md](02_intermediate/vectors.md)

## W

- **wasm** - [04_expert/wasm.md](04_expert/wasm.md)

---

## 版本特性索引

### Rust 1.94 新特性

| 特性 | 文档 | 重要程度 |
|------|------|---------|
| array_windows | [iterators.md](01_fundamentals/iterators.md) | ⭐⭐⭐⭐⭐ |
| LazyCell/LazyLock | [lazy_initialization.md](03_advanced/lazy_initialization.md) | ⭐⭐⭐⭐⭐ |
| char→usize | [type_conversions.md](02_intermediate/type_conversions.md) | ⭐⭐⭐ |
| 数学常量 | [math_constants.md](05_reference/math_constants.md) | ⭐⭐⭐ |
| ControlFlow | [control_flow.md](03_advanced/control_flow.md) | ⭐⭐⭐⭐ |
| Peekable::next_if | [iterators.md](01_fundamentals/iterators.md) | ⭐⭐⭐ |

### Rust 1.95 预览特性

| 特性 | 文档 | 状态 |
|------|------|------|
| gen 关键字 | [generators.md](03_advanced/generators.md) | 🔄 准备中 |
| async trait 完善 | [async/traits.md](03_advanced/async/traits.md) | 🔄 准备中 |

---

**索引生成时间**: 2026-03-19
**版本**: Rust 1.94.0
