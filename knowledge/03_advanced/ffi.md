
### 边界测试：C 可变参数与 Rust 的 FFI 绑定（运行时 UB）

```rust,compile_fail
use std::os::raw::{c_char, c_int};
use std::ffi::CString;

extern "C" {
    fn sprintf(buf: *mut c_char, fmt: *const c_char, ...) -> c_int;
}

fn main() {
    let mut buf = [0u8; 256];
    let fmt = CString::new("%s %d").unwrap();
    let msg = CString::new("hello").unwrap();
    unsafe {
        // ❌ 运行时 UB: 可变参数类型不匹配
        sprintf(buf.as_mut_ptr() as *mut c_char, fmt.as_ptr(), msg.as_ptr(), 42i32);
    }
}
```

> **修正**: C 的**可变参数函数**在 Rust FFI 中绑定是 `unsafe` 的：1) 参数类型不匹配 → UB；2) 格式字符串与参数数量不匹配 → 缓冲区溢出；3) Rust 字符串（UTF-8）与 C 字符串（null-terminated）的编码差异。安全策略：1) 避免直接绑定 C 可变参数函数；2) 使用 `libc` crate 的标准绑定；3) 用 Rust 的 `format!` + `CString::new` 构造参数。`va_list` 在 Rust 中可通过 `c_variadic` feature（nightly）或 `va_list-rs` crate 处理。这与 Go 的 cgo（自动处理部分类型转换）或 Java 的 JNI（JVM 管理类型安全）不同——Rust 的 FFI 是零成本但需完全手动验证。[来源: [The Rustonomicon](https://doc.rust-lang.org/nomicon/ffi.html)] · [来源: [libc crate](https://docs.rs/libc/)]

## 相关主题

- [编译器内部边界测试](./compiler_internals.md) — MIR 优化与 unsafe 语义保留
- [内联汇编](./inline_asm.md) — 输入输出约束与寄存器分配
- [类型驱动正确性](./type_driven_correctness.md) — 类型系统保证的安全边界
