> **Bloom 层级**: 应用 → 分析

### 边界测试：C 可变参数与 Rust 的 FFI 绑定（运行时 UB）

> **📎 交叉引用**
>
> 本主题在 concept 中有深度的概念分析：[FFI](../../concept/03_advanced/05_rust_ffi.md)

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

> **修正**:
> C 的**可变参数函数**在 Rust FFI 中绑定是 `unsafe` 的：
>
> 1) 参数类型不匹配 → UB；
> 2) 格式字符串与参数数量不匹配 → 缓冲区溢出；
> 3) Rust 字符串（UTF-8）与 C 字符串（null-terminated）的编码差异。
>
> 安全策略：
>
> 1) 避免直接绑定 C 可变参数函数；
> 2) 使用 `libc` crate 的标准绑定；
> 3) 用 Rust 的 `format!` + `CString::new` 构造参数。
> `va_list` 在 Rust 中可通过 `c_variadic` feature（nightly）或 `va_list-rs` crate 处理。
> 这与 Go 的 cgo（自动处理部分类型转换）或 Java 的 JNI（JVM 管理类型安全）不同——Rust 的 FFI 是零成本但需完全手动验证。
> [来源: [The Rustonomicon](https://doc.rust-lang.org/nomicon/ffi.html)] ·
> [来源: [libc crate](https://docs.rs/libc/)]

## 相关主题

- [编译器内部边界测试](01_compiler_internals.md) — MIR 优化与 unsafe 语义保留
- [内联汇编](03_inline_asm.md) — 输入输出约束与寄存器分配
- [类型驱动正确性](06_type_driven_correctness.md) — 类型系统保证的安全边界

## 📚 模块 8: 国际化对齐

> 本节按项目模板要求补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 类型 | 说明 |
|:---|:---|:---|
| [Rustonomicon — FFI](https://doc.rust-lang.org/nomicon/ffi.html) | 权威来源 | FFI 官方指南 |
| [The Rust FFI Omnibus](https://jakegoulding.com/rust-ffi-omnibus/) | 权威来源 | FFI 示例 |

### 8.2 学术来源

| 来源 | 类型 | 说明 |
|:---|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | 权威来源 | FFI 边界语义 |

### 8.3 社区权威

| 来源 | 类型 | 说明 |
|:---|:---|:---|
| [bindgen docs](https://rust-lang.github.io/rust-bindgen/) | 权威来源 | C/C++ 绑定生成 |
| [cbindgen docs](https://mozilla.github.io/cbindgen/) | 权威来源 | 生成 C 头文件 |
