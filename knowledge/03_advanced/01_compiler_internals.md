> **Bloom 层级**: 分析 → 评价

### 边界测试：MIR 优化与 unsafe 代码的语义保留（运行时 UB）

```rust,ignore
fn main() {
    let mut x = 0;
    let r = &mut x as *mut i32;
    unsafe {
        *r = 1;
        // ❌ 运行时 UB: 编译器可能基于 &mut x 的独占性假设优化掉 *r 的写入
        // 若编译器认为 r 是从 &mut x 派生的，且 &mut x 已不使用，
        // 可能将 *r 的写入视为死存储消除
        println!("{}", x);
    }
}
```
> **修正**:
> Rust 编译器的 **MIR**（Mid-level IR）优化基于 safe Rust 的语义：
>
> 1) `&mut T` 独占性 → 优化器可假设无其他别名；
> 2) `&T` 不可变性 → 优化器可假设值不变，缓存读取。
> 但在 `unsafe` 块中，若通过裸指针创建别名，优化器可能做出错误假设，导致 UB。
> 防御：
> 3) 从 `&mut T` 创建 `*mut T` 后，不再使用 safe 引用，直到裸指针使用结束；
> 4) 使用 `std::ptr::read_volatile` / `write_volatile`（告诉优化器不要优化）；
> 5) 使用 Miri 检查 Stacked Borrows / Tree Borrows 合规性。
> 这与 C 的 strict aliasing（类似优化假设，但可用 `restrict` 控制）或 LLVM 的 `noalias` 元数据（Rust `&mut` 自动附加）相同
> ——Rust 的优化器假设在 safe 代码中成立，unsafe 代码需手动维护。
> [来源: [Rust Compiler Development](https://rustc-dev-guide.rust-lang.org/mir/index.html)] ·
> [来源: [The Rustonomicon](https://doc.rust-lang.org/nomicon/)]

## 相关主题

- [FFI 边界测试](02_ffi.md) — C 可变参数与 Rust FFI 绑定
- [内联汇编](03_inline_asm.md) — 输入输出约束与编译器优化
- [性能优化](05_performance_optimization.md) — 零成本抽象与编译器优化策略

## 📚 模块 8: 国际化对齐

> 本节按项目模板要求补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 类型 | 说明 |
|:---|:---|:---|
| [Rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/) | 权威来源 | 编译器开发指南 |
| [Rust Reference](https://doc.rust-lang.org/reference/) | 权威来源 | 语言参考 |

### 8.2 学术来源

| 来源 | 类型 | 说明 |
|:---|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | 权威来源 | 编译器语义基础 |
| [a-mir-formality](https://github.com/rust-lang/a-mir-formality) | 权威来源 | 形式化类型系统 |

### 8.3 社区权威

| 来源 | 类型 | 说明 |
|:---|:---|:---|
| [This Week in Rust — Compiler](https://this-week-in-rust.org/) | 权威来源 | 编译器团队动态 |
| [rustc-reading-club](https://github.com/rust-lang/rustc-reading-club) | 权威来源 | rustc 源码共读 |
