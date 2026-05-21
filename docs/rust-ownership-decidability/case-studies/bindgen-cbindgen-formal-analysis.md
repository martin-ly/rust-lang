# Bindgen/Cbindgen FFI绑定形式化分析

> **主题**: C/C++与Rust绑定生成安全
>
> **形式化框架**: ABI兼容 + 所有权映射
>
> **参考**: bindgen Documentation; cbindgen Documentation

---

## 目录
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

- [Bindgen/Cbindgen FFI绑定形式化分析](#bindgencbindgen-ffi绑定形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. Bindgen (C→Rust)](#2-bindgen-crust)
    - [定理 2.1 (类型映射)](#定理-21-类型映射)
    - [定理 2.2 (不安全边界)](#定理-22-不安全边界)
  - [3. Cbindgen (Rust→C)](#3-cbindgen-rustc)
    - [定理 3.1 (公开接口)](#定理-31-公开接口)
  - [4. 所有权映射](#4-所有权映射)
    - [定理 4.1 (Box→指针)](#定理-41-box指针)
  - [5. 布局兼容](#5-布局兼容)
    - [定理 5.1 (repr(C))](#定理-51-reprc)
  - [6. 反例](#6-反例)
    - [反例 6.1 (panic跨越边界)](#反例-61-panic跨越边界)
    - [反例 6.2 (生命周期逃逸)](#反例-62-生命周期逃逸)
  - [*定理数量: 6个*](#定理数量-6个)

---

## 1. 引言
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

FFI绑定工具:

- **Bindgen**: C头文件→Rust绑定
- **Cbindgen**: Rust库→C头文件

---

## 2. Bindgen (C→Rust)
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 定理 2.1 (类型映射)

| C类型 | Rust类型 |
|-------|----------|
| int | c_int |
| char* | *mut c_char |
| struct T | T |
| void* | *mut c_void |

```rust
// 自动生成
extern "C" {
    pub fn open(path: *const c_char, flags: c_int) -> c_int;
}
```

∎

### 定理 2.2 (不安全边界)

> 所有FFI调用标记为unsafe。

```rust
// 原始指针需安全检查
unsafe {
    let fd = open(path.as_ptr(), O_RDONLY);
}
```

∎

---

## 3. Cbindgen (Rust→C)

### 定理 3.1 (公开接口)

> 仅pub且#[no_mangle]函数导出。

```rust
#[no_mangle]
pub extern "C" fn mylib_init() -> *mut Context {
    Box::into_raw(Box::new(Context::new()))
}
```

∎

---

## 4. 所有权映射

### 定理 4.1 (Box→指针)

> Rust Box转换为原始指针传递所有权。

```rust
// Rust侧
pub extern "C" fn create() -> *mut T {
    Box::into_raw(Box::new(T))
}

pub extern "C" fn destroy(ptr: *mut T) {
    if !ptr.is_null() {
        unsafe { Box::from_raw(ptr); }
    }
}
```

∎

---

## 5. 布局兼容

### 定理 5.1 (repr(C))

> 跨FFI的结构需repr(C)。

```rust
#[repr(C)]
pub struct Point {
    x: f64,
    y: f64,
}
```

∎

---

## 6. 反例

### 反例 6.1 (panic跨越边界)

```rust
// 危险: panic可能中止进程
#[no_mangle]
pub extern "C" fn may_panic() {
    panic!("error");  // 未捕获!
}

// 正确: 捕获panic
pub extern "C" fn safe() -> i32 {
    match catch_unwind(|| may_panic()) {
        Ok(_) => 0,
        Err(_) => -1,
    }
}
```

### 反例 6.2 (生命周期逃逸)

```rust
// 危险: 返回借用
pub extern "C" fn get_name() -> *const c_char {
    let s = String::from("test");
    s.as_ptr()  // 悬垂指针!
}

// 正确: 返回拥有数据
pub extern "C" fn get_name() -> *mut c_char {
    CString::new("test").unwrap().into_raw()
}
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)
