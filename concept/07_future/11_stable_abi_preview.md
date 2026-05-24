
### 10.4 边界测试：稳定 ABI 与 extern "C" 的符号兼容性（链接错误）

```rust,compile_fail
// Rust 的默认 ABI 不稳定（随编译器版本变化）
#[no_mangle]
pub extern "C" fn rust_function(x: i32) -> i32 {
    x * 2
}

// ❌ 链接错误: 若 C 代码按 Rust 默认 ABI 调用（而非 extern "C"）
// C 代码:
// int rust_function(int x); // 声明匹配 extern "C"
// // 但 C++ 的 name mangling 可能与 Rust 的 #[no_mangle] 冲突

fn main() {}
```

> **修正**: **稳定 ABI** 是 Rust 的长期目标：1) 当前 `extern "C"` 是唯一稳定的跨语言 ABI；2) Rust 的默认 ABI（`extern "Rust"`）随编译器版本变化（字段重排、enum 布局优化）；3) `#[repr(C)]` 强制 C 兼容布局，但仍有限制（如 enum 的大小）。`crabi`（C Rust ABI）提案：1) 定义 Rust 类型在 FFI 中的稳定布局；2) 与 C ABI 兼容但支持 Rust 特性（如 panic、trait object）；3) 允许 Rust 动态库跨版本安全链接。当前限制：1) `String` / `Vec` 不能安全传递（需 `CString` / 原始指针）；2) `panic` 跨 FFI 边界是 UB；3) `Drop` 在 FFI 中的行为未定义。这与 C++ 的 ABI（由 Itanium/MSVC 定义，稳定但不跨编译器）或 Swift 的 ABI（稳定但版本锁定）不同——Rust 追求语言级别的稳定 ABI，而非依赖平台约定。[来源: [crabi Proposal](https://rust-lang.github.io/rfcs/3325-crabi.html)] · [来源: [Rust FFI](https://doc.rust-lang.org/nomicon/ffi.html)]
