> **内容分级**: [参考级]
>
# 异常安全：C++ 与 Rust 的错误处理哲学
>
> **EN**: Exception Safety: C++ vs Rust
> **Summary**: A deep comparison of exception safety guarantees in C++ (strong/basic/no-throw) and Rust's error-handling model (Result, panic, Drop).
>
> **受众**: [进阶]
> **层级**: L2 进阶概念
> **A/S/P 标记**: C+A — Comparison + Application
> **双维定位**: C×Ana
> **前置概念**: [Error Handling](04_error_handling.md) · [Error Handling Basics](../01_foundation/32_error_handling_basics.md) · [Ownership](../01_foundation/01_ownership.md)
> **后置概念**: [Error Handling Deep Dive](16_error_handling_deep_dive.md) · [Rust vs C++](../05_comparative/01_rust_vs_cpp.md)
> **主要来源**: · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Rust Reference — Runtime and Unwinding](https://doc.rust-lang.org/reference/runtime.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
>
> [Brown University CRP — Exceptions](https://cel.cs.brown.edu/crp/idioms/exceptions.html) ·
> [Google Comprehensive Rust — C++ Exception](https://google.github.io/comprehensive-rust/android/interoperability/cpp/cpp-exception.html) ·
> [TRPL Ch 9 — Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html) ·
> [cppreference — Exceptions](https://en.cppreference.com/w/cpp/language/exceptions) ·
> [cppreference — noexcept](https://en.cppreference.com/w/cpp/language/noexcept)
>
---

> **Bloom 层级**: 分析 → 评价

## 一、核心命题

> **C++ 和 Rust 对"程序出错时如何保持状态一致"给出了两套完全不同的答案。
> C++ 依赖异常传播机制，并通过 strong / basic / no-throw guarantee 描述异常发生时的状态保证；
> Rust 将可恢复错误编码进类型系统（Type System）（`Result<T, E>`），将不可恢复错误隔离为 panic，并通过所有权（Ownership）规则保证资源释放（`Drop`）。**

---

## 二、C++ 的异常保证体系

### 2.1 三种异常保证

C++ 标准库和工程中常用以下分类描述函数在异常发生时的行为（cppreference: [Exception safety guarantees](https://en.cppreference.com/w/cpp/language/exceptions#Exception_safety)）：

| 保证级别 | 定义 | 工程含义 |
|:---|:---|:---|
| **No-throw guarantee** | 函数保证不抛出任何异常 | 可用于析构函数、移动操作、关键回滚路径 |
| **Strong guarantee** | 如果函数抛出异常，程序状态回滚到调用前 | 类似事务的原子性，实现成本高 |
| **Basic guarantee** | 如果函数抛出异常，程序状态保持有效（不变量成立）但不保证与调用前相同 | 最低可接受的异常安全级别 |
| **No guarantee** | 不保证任何状态 | 应避免在健壮代码中出现 |

### 2.2 C++ 异常传播与栈展开

```cpp
void f() {
    auto r = acquire_resource();
    g(); // 若 g() 抛出异常，栈展开会调用 r 的析构函数
}
```

C++ 异常传播依赖**栈展开（stack unwinding）**：从抛出点向上遍历调用栈，调用沿途局部对象的析构函数，直到找到匹配的 catch 块。

### 2.3 析构函数中抛异常的危险

```cpp
struct Bad {
    ~Bad() { throw std::runtime_error("boom"); }
};

void f() {
    Bad b;
    throw std::runtime_error("outer"); // 栈展开时调用 ~Bad()，~Bad() 又抛异常
} // std::terminate
```

C++ 中，**析构函数抛异常会导致 `std::terminate`**。因此析构函数必须标记为 `noexcept`（隐式或显式）。

---

## 三、Rust 的错误处理模型

### 3.1 可恢复错误：`Result<T, E>`

```rust
fn divide(a: f64, b: f64) -> Result<f64, &'static str> {
    if b == 0.0 {
        Err("division by zero")
    } else {
        Ok(a / b)
    }
}

fn main() {
    match divide(10.0, 0.0) {
        Ok(v) => println!("{}", v),
        Err(e) => eprintln!("error: {}", e),
    }
}
```

Rust 将可恢复错误编码进返回类型（TRPL: [Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)）。调用者必须显式处理 `Err` 分支，不存在"异常未被捕获就向上传播"的情况。

### 3.2 传播运算符 `?`

```rust
fn read_config(path: &str) -> Result<Config, std::io::Error> {
    let content = std::fs::read_to_string(path)?; //  early return Err
    Ok(Config::parse(&content)?)
}
```

`?` 运算符提供类似异常传播的便利性，但受类型系统约束：只能在返回 `Result`、`Option` 或实现 `Try` 的类型的函数中使用。

### 3.3 不可恢复错误：panic

```rust
fn main() {
    panic!("unrecoverable");
}
```

Rust 的 panic 用于不可恢复错误（Rust Reference: [Macro std::panic](https://doc.rust-lang.org/std/macro.panic.html)）。默认情况下会展开栈并调用析构函数，但也可以配置为立即 abort。panic 不应用于常规错误处理（Error Handling）。

---

## 四、核心对比

| 维度 | C++ | Rust |
|:---|:---|:---|
| 可恢复错误机制 | 异常（`throw` / `catch`） | `Result<T, E>` 作为返回类型 |
| 错误传播 | 自动沿栈向上传播 | 显式 `?` 运算符或 `match` |
| 异常保证 | strong / basic / no-throw | 通过类型系统保证：失败路径显式 |
| 析构函数失败 | 会导致 `std::terminate` | `Drop::drop` 签名 `fn drop(&mut self)`，不可返回错误 |
| 资源释放 | RAII + 栈展开 | RAII + 所有权转移 + `Drop` |
| 不可恢复错误 | 异常可被捕获，也可未捕获导致 `std::terminate` | `panic!` 明确用于不可恢复场景 |
| 编译期检查 | 无（异常规格 `throw()` 已被移除） | `Result` 必须被处理或传播 |

---

## 五、`Drop` 的不可失败性

Rust 的 `Drop` trait  deliberately 不能失败：

```rust
pub trait Drop {
    fn drop(&mut self);
}
```

这与 C++ 析构函数类似（实际中也不应抛异常），但 Rust 在类型层面强制保证：

- `drop` 返回 `()`，没有 `Result` 返回类型。
- 如果在 `drop` 中调用可能失败的操作，必须内部处理错误（如记录日志、忽略或 panic）。
- 这消除了 C++ 中"析构函数抛异常导致 terminate"的整类问题。

---

## 六、C++23 `std::expected` vs Rust `Result`

C++23 引入 `std::expected<T, E>`，显式向 Rust 的 `Result` 靠拢：

```cpp
#include <expected>

std::expected<int, std::string> parse_int(const std::string& s) {
    try {
        return std::stoi(s);
    } catch (...) {
        return std::unexpected("parse failed");
    }
}
```

| 特性 | C++23 `std::expected` | Rust `Result<T, E>` |
|:---|:---|:---|
| 编译器强制处理 | 否 | 是（未使用 Result 会警告） |
| 传播语法 | 手动或 `and_then` | `?` 运算符 |
| 与现有异常生态 | 可混合使用 | 与 panic 严格区分 |
| 模式匹配（Pattern Matching） | C++17 `if` 初始化器或 C++23 `std::visit` | `match` / `if let` |

---

## 七、形式化视角

C++ 的异常安全保证可以形式化为**关于计算前后状态的关系**：

- **No-throw**: `∀s. exec(f, s) ≠ ⊥`
- **Strong**: `exec(f, s) = ⊥ ⟹ state = s`
- **Basic**: `exec(f, s) = ⊥ ⟹ invariant(state)`

Rust 的 `Result<T, E>` 把异常安全的**状态关系**编码为**类型关系**：

```text
f: S -> Result<S', E>
```

成功时返回新状态 `S'`，失败时返回错误 `E`，原状态 `S` 由所有权规则决定是被消费、保留还是部分修改。

---

## 八、总结

- **L1**：C++ 用异常处理错误，需要 strong/basic/no-throw 保证；Rust 用 `Result` 显式编码错误，`panic` 用于不可恢复错误。
- **L2**：Rust 的 `Drop` 不可失败，消除了 C++ 析构函数抛异常导致 `std::terminate` 的问题；`?` 运算符提供类似异常传播的便利但受类型约束。
- **L3**：C++ 异常安全是关于"状态不变量"的运行时（Runtime）/约定保证；Rust 将错误处理转化为类型系统的分支显式化，使异常安全从"约定"变为"可静态检查的结构"。

---

## 九、延伸阅读

- [TRPL: Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [Rust Reference: panic! macro](https://doc.rust-lang.org/std/macro.panic.html)
- [Brown University CRP — Exceptions](https://cel.cs.brown.edu/crp/idioms/exceptions.html)
- [Google Comprehensive Rust — C++ Exception](https://google.github.io/comprehensive-rust/android/interoperability/cpp/cpp-exception.html)
- [cppreference: Exceptions](https://en.cppreference.com/w/cpp/language/exceptions)
- [cppreference: noexcept specifier](https://en.cppreference.com/w/cpp/language/noexcept)
- [cppreference: Exception safety guarantees](https://en.cppreference.com/w/cpp/language/exceptions#Exception_safety)
