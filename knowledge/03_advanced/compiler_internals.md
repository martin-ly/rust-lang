
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

> **修正**: Rust 编译器的 **MIR**（Mid-level IR）优化基于 safe Rust 的语义：1) `&mut T` 独占性 → 优化器可假设无其他别名；2) `&T` 不可变性 → 优化器可假设值不变，缓存读取。但在 `unsafe` 块中，若通过裸指针创建别名，优化器可能做出错误假设，导致 UB。防御：1) 从 `&mut T` 创建 `*mut T` 后，不再使用 safe 引用，直到裸指针使用结束；2) 使用 `std::ptr::read_volatile` / `write_volatile`（告诉优化器不要优化）；3) 使用 Miri 检查 Stacked Borrows / Tree Borrows 合规性。这与 C 的 strict aliasing（类似优化假设，但可用 `restrict` 控制）或 LLVM 的 `noalias` 元数据（Rust `&mut` 自动附加）相同——Rust 的优化器假设在 safe 代码中成立，unsafe 代码需手动维护。[来源: [Rust Compiler Development](https://rustc-dev-guide.rust-lang.org/mir/index.html)] · [来源: [The Rustonomicon](https://doc.rust-lang.org/nomicon/)]
