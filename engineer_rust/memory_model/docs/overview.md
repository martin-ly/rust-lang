# 内存模型（Memory Model）

## 1. 工程原理与定义（Principle & Definition）

内存模型描述程序如何分配、访问和释放内存，直接影响安全性和性能。Rust 通过所有权、借用和生命周期静态保证内存安全。
Memory model describes how programs allocate, access, and release memory, directly impacting safety and performance. Rust statically guarantees memory safety via ownership, borrowing, and lifetimes.

## 2. Rust 1.88 新特性工程化应用

- `&raw`指针操作符：安全创建原始指针，便于底层优化。
- `inline const`：支持常量表达式内嵌，提升编译期计算能力。
- LazyCell/LazyLock：线程安全的惰性初始化。

## 3. 典型场景与最佳实践（Typical Scenarios & Best Practices）

- 使用 `Box`/`Rc`/`Arc` 管理堆内存。
- `Cell`/`RefCell` 实现内部可变性。
- `unsafe` 块进行底层优化，配合 `&raw` 保证安全。
- `miri` 工具检测未定义行为。

**最佳实践：**

- 优先使用安全抽象管理内存。
- 仅在必要时使用 unsafe，并配合工具检测。
- 利用生命周期参数防止悬垂指针。
- 结合自动化测试覆盖边界情况。

## 4. 常见问题 FAQ

- Q: Rust 如何保证内存安全？
  A: 通过所有权、借用和生命周期静态检查，绝大多数内存错误在编译期被消除。
- Q: 何时需要使用 unsafe？
  A: 仅在性能敏感或底层接口场景下，且需严格边界管理。
- Q: 如何检测未定义行为？
  A: 使用 miri 工具进行动态检测。

## 5. 参考与扩展阅读

- [Rust 官方内存管理文档](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [miri 内存模型检测工具](https://github.com/rust-lang/miri)
