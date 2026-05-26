> **Bloom 层级**: 应用 → 分析

### 边界测试：内联汇编的输入输出约束错误（编译错误/运行时 UB）

```rust,ignore
fn main() {
    let mut x: u64 = 42;
    unsafe {
        // ❌ 编译错误: 约束字符串格式错误
        // std::arch::asm!(
        //     "mov {0}, {1}",
        //     out(reg) x,
        //     in(reg) 100,
        // );

        // 正确:
        std::arch::asm!(
            "add {0}, {1}",
            inout(reg) x,
            in(reg) 100,
        );
    }
    assert_eq!(x, 142);
}
```

> **修正**: Rust 的内联汇编（`asm!` macro，1.59+ stable）要求精确的**约束**（constraints）：1) `in(reg)` — 输入寄存器；2) `out(reg)` — 输出寄存器；3) `inout(reg)` — 输入输出共用；4) `lateout` — 输出在输入使用后写入。错误约束导致：1) 编译错误（约束不匹配操作数类型）；2) 运行时 UB（编译器错误分配寄存器，覆盖重要数据）。高级用法：`sym`（符号引用）、`label`（汇编标签）、`options`（`pure`、`nomem`、`readonly` 等优化提示）。这与 C 的 `asm`（GCC 风格，约束语法类似但平台相关）或 Go 的 `asm`（独立 `.s` 文件，非内联）不同——Rust 的内联汇编是跨平台的抽象，但底层仍依赖 LLVM 的集成汇编器。[来源: [Rust Reference — Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)] · [来源: [Rust Inline Assembly](https://doc.rust-lang.org/nightly/unstable-book/language-features/asm.html)]

## 相关主题

- [FFI 边界测试](./ffi.md) — C 可变参数与 Rust FFI 绑定
- [编译器内部边界测试](./compiler_internals.md) — MIR 优化与 unsafe 语义保留
- [延迟初始化](./lazy_initialization.md) — 运行时资源管理模式
