# FFI (Foreign Function Interface)

> **EN**: FFI Foreign Function Interface
> **Summary**: FFI (Foreign Function Interface) FFI Foreign Function Interface. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/03_advanced/04_ffi/05_rust_ffi.md](../../../concept/03_advanced/04_ffi/05_rust_ffi.md)。
> **历史版本存档**: [archive/knowledge/03_advanced/unsafe/01_ffi.md](../../../archive/knowledge/03_advanced/unsafe/01_ffi.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. 使用 `extern "C"` 声明外部函数，`unsafe` 块调用
2. `#[no_mangle]` / `pub extern "C"` 暴露 Rust 符号给 C
3. 类型映射必须遵循 C ABI（如 `c_int`, `*mut T`）
4. 跨越 FFI 边界需保证 panic 安全与内存布局一致

## 关键区分

| 方向 | 机制 | 安全责任 |
|---|---|---|
| Rust 调用 C | `extern` + `unsafe` | 调用方保证 |
| C 调用 Rust | `#[no_mangle]` + `extern "C"` | Rust 端保证 |

## 常见陷阱

- 忽略 C 端内存所有权导致 use-after-free
- 在 FFI 边界 panic 跨越到 C 导致 UB
- 结构体布局假设不匹配（需 `repr(C)`）

---

**详细内容已迁移**：请点击上方 [concept/03_advanced/04_ffi/05_rust_ffi.md](../../../concept/03_advanced/04_ffi/05_rust_ffi.md) 查看最新权威解释。
