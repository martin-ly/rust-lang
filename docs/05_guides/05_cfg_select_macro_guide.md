# `cfg_select!` 宏完全指南 {#cfg_select-宏完全指南}

<!-- canonical-normalized 2026-07-11 -->
> **权威来源（Canonical）**: 本文件为 `cfg_select!` 宏的工程使用指南（场景/陷阱/决策，独特内容）；`cfg_select!` 与条件编译的通用概念解释请以 concept 权威页为准：[`concept/03_advanced/03_proc_macros/28_conditional_compilation.md`](../../concept/03_advanced/03_proc_macros/28_conditional_compilation.md)
>
> 根据 AGENTS.md §2 Canonical 规则：本文仅保留本文独特内容（基本语法速查、4 类使用场景、与 `#[cfg]`/`cfg!` 对比、嵌套与常量上下文等高级模式、4 类常见陷阱与反例），不重复 concept/ 中的条件编译概念定义、规则与定理推导。

> **EN**: Cfg Select Macro Guide
> **Summary**: cfg_select! 宏完全指南 Cfg Select Macro Guide.
> **分级**: [A]
> **Bloom 层级**: L2-L3
> **稳定版本**: Rust 1.95.0
> **适用版本**: 1.95.0+
> **Edition**: 任意 Edition
>
> **受众**: [进阶] / [专家]
> **内容分级**: [专家级]

---

## 目录 {#目录}

- [`cfg_select!` 宏完全指南 {#cfg\_select-宏完全指南}](#cfg_select-宏完全指南-cfg_select-宏完全指南)
  - [目录 {#目录}](#目录-目录)
  - [一、什么是 `cfg_select!` {#一什么是-cfg\_select}](#一什么是-cfg_select-一什么是-cfg_select)
    - [核心解决的问题 {#核心解决的问题}](#核心解决的问题-核心解决的问题)
  - [二、基本语法 {#二基本语法}](#二基本语法-二基本语法)
    - [规则 {#规则}](#规则-规则)
    - [最小示例 {#最小示例}](#最小示例-最小示例)
  - [三、使用场景与示例 {#三使用场景与示例}](#三使用场景与示例-三使用场景与示例)
    - [场景 1：平台相关的常量值 {#场景-1平台相关的常量值}](#场景-1平台相关的常量值-场景-1平台相关的常量值)
    - [场景 2：平台相关的类型别名 {#场景-2平台相关的类型别名}](#场景-2平台相关的类型别名-场景-2平台相关的类型别名)
    - [场景 3：功能特性的默认配置 {#场景-3功能特性的默认配置}](#场景-3功能特性的默认配置-场景-3功能特性的默认配置)
    - [场景 4：与 `match` 结合 {#场景-4与-match-结合}](#场景-4与-match-结合-场景-4与-match-结合)
  - [四、与 `#[cfg]` 的对比 {#四与-cfg-的对比}](#四与-cfg-的对比-四与-cfg-的对比)
    - [什么时候用 `#[cfg]`？ {#什么时候用-cfg}](#什么时候用-cfg-什么时候用-cfg)
    - [什么时候用 `cfg_select!`？ {#什么时候用-cfg\_select}](#什么时候用-cfg_select-什么时候用-cfg_select)
  - [五、高级模式 {#五高级模式}](#五高级模式-五高级模式)
    - [模式 1：嵌套 `cfg_select!` {#模式-1嵌套-cfg\_select}](#模式-1嵌套-cfg_select-模式-1嵌套-cfg_select)
    - [模式 2：与 `cfg!` 宏对比 {#模式-2与-cfg-宏对比}](#模式-2与-cfg-宏对比-模式-2与-cfg-宏对比)
    - [模式 3：在常量上下文中使用 {#模式-3在常量上下文中使用}](#模式-3在常量上下文中使用-模式-3在常量上下文中使用)
  - [六、常见陷阱 {#六常见陷阱}](#六常见陷阱-六常见陷阱)
    - [陷阱 1：忘记 `_ =>` 兜底分支 {#陷阱-1忘记-\_-兜底分支}](#陷阱-1忘记-_--兜底分支-陷阱-1忘记-_-兜底分支)
    - [陷阱 2：分支类型不一致 {#陷阱-2分支类型不一致}](#陷阱-2分支类型不一致-陷阱-2分支类型不一致)
    - [陷阱 3：在运行时条件中使用 {#陷阱-3在运行时条件中使用}](#陷阱-3在运行时条件中使用-陷阱-3在运行时条件中使用)
    - [陷阱 4：过度使用导致可读性下降 {#陷阱-4过度使用导致可读性下降}](#陷阱-4过度使用导致可读性下降-陷阱-4过度使用导致可读性下降)
  - [七、参考 {#七参考}](#七参考-七参考)
    - [相关文档 {#相关文档}](#相关文档-相关文档)

---

## 一、什么是 `cfg_select!` {#一什么是-cfg_select}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

`cfg_select!` 是 Rust 1.95.0 稳定化的编译期条件选择宏。
它允许在表达式上下文中根据 `cfg` 条件选择不同的值，**无需代码重复**。

### 核心解决的问题 {#核心解决的问题}

传统 `#[cfg]` 属性只能在**语句/项级别**使用：

```rust
#[cfg(target_os = "linux")]
fn os_name() -> &'static str { "Linux" }

#[cfg(target_os = "windows")]
fn os_name() -> &'static str { "Windows" }

#[cfg(not(any(target_os = "linux", target_os = "windows")))]
fn os_name() -> &'static str { "Unknown" }
```

`cfg_select!` 允许在**表达式级别**直接选择：

```rust
let name = cfg_select! {
    target_os = "linux" => "Linux",
    target_os = "windows" => "Windows",
    _ => "Unknown",
};
```

---

## 二、基本语法 {#二基本语法}

```rust
cfg_select! {
    cfg_predicate1 => expression1,
    cfg_predicate2 => expression2,
    ...
    _ => fallback_expression,
}
```

### 规则 {#规则}

| 规则 | 说明 |
|------|------|
| 谓词语法 | 与 `#[cfg(...)]` 完全相同 |
|  exhaustiveness | 必须包含 `_ =>` 兜底分支 |
| 类型一致性（Coherence） | 所有分支表达式类型必须相同 |
| 求值时机 | **编译期**求值，零运行时开销 |

### 最小示例 {#最小示例}

```rust
use std::cfg_select;

fn main() {
    let ptr_size = cfg_select! {
        target_pointer_width = "64" => 8_usize,
        target_pointer_width = "32" => 4_usize,
        _ => panic!("unsupported pointer width"),
    };
    println!("Pointer size: {} bytes", ptr_size);
}
```

---

## 三、使用场景与示例 {#三使用场景与示例}

### 场景 1：平台相关的常量值 {#场景-1平台相关的常量值}

```rust
use std::cfg_select;

const PATH_SEPARATOR: char = cfg_select! {
    target_family = "windows" => '\\',
    _ => '/',
};

const LINE_ENDING: &'static str = cfg_select! {
    target_family = "windows" => "\r\n",
    _ => "\n",
};
```

### 场景 2：平台相关的类型别名 {#场景-2平台相关的类型别名}

```rust
use std::cfg_select;

type NativeSocket = cfg_select! {
    target_family = "unix" => std::os::unix::net::UnixStream,
    target_family = "windows" => std::os::windows::net::...,
    _ => std::net::TcpStream,
};
```

### 场景 3：功能特性的默认配置 {#场景-3功能特性的默认配置}

```rust
use std::cfg_select;

const DEFAULT_BUFFER_SIZE: usize = cfg_select! {
    target_arch = "wasm32" => 1024,      // WASM 内存受限
    target_os = "embedded" => 256,       // 嵌入式资源紧张
    _ => 8192,                            // 桌面/服务器默认
};
```

### 场景 4：与 `match` 结合 {#场景-4与-match-结合}

```rust
use std::cfg_select;

fn handle_error(code: u32) -> &'static str {
    let category = cfg_select! {
        target_os = "linux" => "linux-error",
        target_os = "windows" => "win-error",
        _ => "generic-error",
    };

    match category {
        "linux-error" => match code {
            2 => "No such file or directory",
            13 => "Permission denied",
            _ => "Unknown Linux error",
        },
        "win-error" => match code {
            2 => "The system cannot find the file specified",
            5 => "Access is denied",
            _ => "Unknown Windows error",
        },
        _ => "Unknown error",
    }
}
```

---

## 四、与 `#[cfg]` 的对比 {#四与-cfg-的对比}

| 维度 | `#[cfg]` | `cfg_select!` |
|------|---------|--------------|
| **作用域** | 项级别（函数、模块（Module）、结构体（Struct）） | 表达式级别 |
| **代码重复** | 高（需为每种条件写完整项） | 低（单表达式内分支） |
| **可读性** | 中等（分散在多个 `#[cfg]` 块中） | 高（条件与值紧邻） |
| **IDE 支持** | 良好（灰色显示未激活代码） | 良好 |
| **适用场景** | 条件编译整个模块（Module）/函数 | 条件选择值/小表达式 |
| **运行时开销** | 零 | 零 |

### 什么时候用 `#[cfg]`？ {#什么时候用-cfg}

- 整个函数/模块在不同平台完全不同
- 需要条件编译掉大量代码以减少二进制体积

### 什么时候用 `cfg_select!`？ {#什么时候用-cfg_select}

- 只需要根据条件选择**一个值**
- 希望将平台差异集中在单一表达式中
- 避免代码重复

---

## 五、高级模式 {#五高级模式}

### 模式 1：嵌套 `cfg_select!` {#模式-1嵌套-cfg_select}

```rust
use std::cfg_select;

fn get_allocator() -> &'static str {
    cfg_select! {
        target_os = "linux" => cfg_select! {
            target_arch = "x86_64" => "jemalloc",
            _ => "system",
        },
        target_os = "windows" => "system",
        _ => "default",
    }
}
```

### 模式 2：与 `cfg!` 宏对比 {#模式-2与-cfg-宏对比}

```rust
// cfg! 返回 bool，适合简单判断
if cfg!(target_os = "linux") {
    // ...
}

// cfg_select! 返回具体值，适合多分支选择
let strategy = cfg_select! {
    target_os = "linux" => LinuxStrategy,
    target_os = "windows" => WindowsStrategy,
    target_os = "macos" => MacStrategy,
    _ => GenericStrategy,
};
```

### 模式 3：在常量上下文中使用 {#模式-3在常量上下文中使用}

```rust
use std::cfg_select;

const IS_LITTLE_ENDIAN: bool = cfg_select! {
    target_endian = "little" => true,
    _ => false,
};

const CACHE_LINE_SIZE: usize = cfg_select! {
    target_arch = "x86_64" => 64,
    target_arch = "aarch64" => 64,
    target_arch = "riscv64" => 64,
    _ => 32,
};
```

---

## 六、常见陷阱 {#六常见陷阱}

### 陷阱 1：忘记 `_ =>` 兜底分支 {#陷阱-1忘记-_-兜底分支}

```rust
// ❌ 错误：缺少兜底分支
cfg_select! {
    target_os = "linux" => "Linux",
    target_os = "windows" => "Windows",
    // 编译错误：未覆盖所有情况
}
```

### 陷阱 2：分支类型不一致 {#陷阱-2分支类型不一致}

```rust
// ❌ 错误：类型不匹配
cfg_select! {
    target_os = "linux" => 1_u32,
    _ => "unknown",  // 错误：expected u32, found &str
}
```

### 陷阱 3：在运行时条件中使用 {#陷阱-3在运行时条件中使用}

```rust
// ❌ 错误：cfg_select! 是编译期宏
let runtime_os = std::env::consts::OS;
cfg_select! {
    target_os = runtime_os => ...,  // 错误：cfg 条件必须是编译期常量
}
```

### 陷阱 4：过度使用导致可读性下降 {#陷阱-4过度使用导致可读性下降}

```rust
// ❌ 反面教材：过于复杂的嵌套
let x = cfg_select! {
    all(target_os = "linux", target_arch = "x86_64", target_feature = "sse2") => {
        cfg_select! {
            target_endian = "little" => v1,
            _ => v2,
        }
    },
    ...
};

// ✅ 建议：提取为命名常量或函数
const VALUE: u32 = cfg_select! { ... };
```

---

## 七、参考 {#七参考}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**

| 资源 | 链接 |
|------|------|
| `cfg_select!` 文档 | <https://doc.rust-lang.org/std/macro.cfg_select.html> |
| Rust 1.95.0 Release Notes | <https://releases.rs/docs/1.95.0/> |
| `#[cfg]` 参考 | <https://doc.rust-lang.org/reference/conditional-compilation.html> |
| RFC (如适用) | 见 tracking issue |

### 相关文档 {#相关文档}

- [Rust 1.95 特性速查表](../02_reference/quick_reference/02_rust_195_features_cheatsheet.md)
- [Rust 版本跟踪](../../concept/07_future/00_version_tracking/05_rust_version_tracking.md)
- [2024 Edition 迁移指南](../../knowledge/06_ecosystem/02_edition_2024.md)
