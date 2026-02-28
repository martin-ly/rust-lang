# ABI 速查卡

> **文档类型**: 快速参考
> **难度**: ⭐⭐⭐ 中级
> **最后更新**: 2026-02-28

---

## 📋 目录

- [ABI 速查卡](#abi-速查卡)
  - [📋 目录](#-目录)
  - [什么是 ABI](#什么是-abi)
  - [Rust 中的 ABI 字符串](#rust-中的-abi-字符串)
  - [平台默认 ABI](#平台默认-abi)
  - [常见 ABI 对比](#常见-abi-对比)
    - [x86\_64 平台](#x86_64-平台)
    - [x86 (32-bit) 平台](#x86-32-bit-平台)
  - [使用示例](#使用示例)
  - [ABI 与类型布局](#abi-与类型布局)

## 什么是 ABI

ABI (Application Binary Interface) 定义了函数调用约定、数据布局和系统调用接口。

---

## Rust 中的 ABI 字符串

| ABI 字符串 | 描述 | 使用场景 |
|-----------|------|---------|
| `"C"` | C 调用约定 | 默认的 FFI 选择 |
| `"system"` | 系统默认 | Windows API |
| `"stdcall"` | 标准调用 | Win32 API |
| `"fastcall"` | 快速调用 | 某些优化场景 |
| `"vectorcall"` | 向量调用 | Windows SIMD |
| `"win64"` | Windows x64 | Windows 64位 |
| `"sysv64"` | System V AMD64 | Linux/macOS 64位 |
| `"aapcs"` | ARM 过程调用 | ARM 架构 |
| `"C-unwind"` | C + 栈展开 | 跨语言异常 |

---

## 平台默认 ABI

```rust
// 跨平台写法
#[cfg(target_os = "windows")]
type PlatformAbi = extern "system";

#[cfg(not(target_os = "windows"))]
type PlatformAbi = extern "C";

PlatformAbi fn platform_function() {}
```

---

## 常见 ABI 对比

### x86_64 平台

| ABI | 寄存器传递 | 栈清理 | 平台 |
|-----|-----------|-------|------|
| `sysv64` | RDI, RSI, RDX, RCX, R8, R9 | 调用者 | Linux/macOS |
| `win64` | RCX, RDX, R8, R9 | 调用者 | Windows |

### x86 (32-bit) 平台

| ABI | 参数传递 | 栈清理 |
|-----|---------|-------|
| `cdecl` | 栈 | 调用者 |
| `stdcall` | 栈 | 被调用者 |
| `fastcall` | ECX, EDX + 栈 | 被调用者 |

---

## 使用示例

```rust
// 标准 C ABI
extern "C" fn c_abi_function(x: i32) -> i32 {
    x * 2
}

// Windows API 使用 system
extern "system" fn windows_callback() {}

// 自定义 ABI
extern "stdcall" fn stdcall_fn() {}

// 可变参数必须使用 C ABI
extern "C" fn varargs(fmt: *const c_char, ...) {}
```

---

## ABI 与类型布局

```rust
#[repr(C)]  // C 兼容布局
struct CCompatible {
    a: u32,
    b: u16,
}

#[repr(transparent)]  // 与内部类型相同 ABI
struct Wrapper(u64);
```

---

**快速提示**: 不确定时用 `"C"`，Windows API 用 `"system"`。
