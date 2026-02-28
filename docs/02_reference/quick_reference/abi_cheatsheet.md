# Rust ABI 速查卡

> 快速参考 Rust 中所有可用的调用约定 (Calling Conventions)

---

## 完整 ABI 列表

| ABI | 平台 | 用途 | 典型场景 |
|-----|------|------|----------|
| `"Rust"` | 所有 | 默认 ABI | 普通 Rust 函数 |
| `"C"` | 所有 | C 调用约定 | FFI, 大多数 C 库 |
| `"system"` | 依平台 | 系统调用约定 | Windows API |
| `"stdcall"` | Windows x86 | Pascal 风格 | Win32 API (32位) |
| `"fastcall"` | Windows | 寄存器传参 | 性能敏感代码 |
| `"vectorcall"` | Windows | SIMD 优化 | DirectX Math |
| `"cdecl"` | x86 | C 风格 (调用者清栈) | C/C++ 库 |
| `"thiscall"` | MSVC x86 | C++ 成员函数 | C++ 互操作 |
| `"aapcs"` | ARM | ARM 过程调用标准 | ARM 嵌入式 |
| `"win64"` | Windows x64 | Windows x64 约定 | Windows 64位 FFI |
| `"sysv64"` | Linux/macOS x64 | System V AMD64 ABI | Unix 64位 FFI |
| `"wasm"` | WebAssembly | WASM C ABI | WebAssembly |

---

## 平台特定推荐

### Windows

```rust
// Windows API (自动选择 32/64位)
extern "system" {
    fn GetLastError() -> u32;
}

// Windows x86 (遗留)
extern "stdcall" {
    fn MessageBoxA(hwnd: *const c_void, text: *const c_char, 
                   caption: *const c_char, type_: u32) -> i32;
}

// Windows x64
extern "win64" {
    fn custom_dll_function(x: i64) -> i64;
}
```

### Linux / macOS

```rust
// Unix 系统标准
extern "C" {
    fn printf(format: *const c_char, ...) -> i32;
}

// x86_64 优化
extern "sysv64" {
    fn optimized_function(x: f64, y: f64) -> f64;
}
```

### ARM

```rust
// ARM 32位
extern "aapcs" {
    fn arm_specific_func(x: i32) -> i32;
}

// AArch64 使用 "C" (与 AAPCS64 相同)
extern "C" {
    fn aarch64_func(x: i64) -> i64;
}
```

---

## ABI 对比

### x86_64 对比

| 特性 | sysv64 (Linux/macOS) | win64 (Windows) |
|------|---------------------|-----------------|
| 整数寄存器 | RDI, RSI, RDX, RCX, R8, R9 | RCX, RDX, R8, R9 |
| 浮点寄存器 | XMM0-XMM7 | XMM0-XMM3 |
| 栈清理 | 调用者 | 调用者 |
| 可变参数 | AL 寄存器计数 | 不适用 |

### 32位对比

| ABI | 传参方式 | 栈清理 | 使用场景 |
|-----|----------|--------|----------|
| cdecl | 栈 | 调用者 | 通用 C |
| stdcall | 栈 | 被调用者 | Win32 API |
| fastcall | ECX, EDX + 栈 | 被调用者 | 性能优化 |

---

## 陷阱与注意

| 陷阱 | 说明 |
|------|------|
| `extern "C"` vs `extern "system"` | Windows 上 `"system"` = `"stdcall"` (x86) 或 `"win64"` (x64) |
| `#[no_mangle]` | FFI 函数通常需要避免名称修饰 |
| `repr(C)` | 结构体跨 FFI 时需要 C 内存布局 |
| `panic=abort` | FFI 边界建议禁用 panic 展开 |

---

**最后更新**: 2026-02-28
