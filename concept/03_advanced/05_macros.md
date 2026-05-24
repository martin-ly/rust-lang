
### 10.4 边界测试：declarative macro 的 hygiene 与标识符泄漏（编译错误）

```rust,ignore
macro_rules! leaky_macro {
    ($val:expr) => {
        let internal_var = $val;
        println!("{}", internal_var);
    };
}

fn main() {
    leaky_macro!(42);
    // ❌ 编译错误: Rust 的 macro hygiene 防止标识符泄漏
    // internal_var 在宏展开后不可见
    // println!("{}", internal_var);
}
```

> **修正**: **Macro hygiene**（卫生宏）是 Rust 宏系统的核心特性：1) 宏内部定义的标识符不会与外部冲突；2) 宏参数中的标识符也不会捕获外部同名变量；3) 与 C 的宏（纯文本替换，无 hygiene）完全不同。显式打破 hygiene：1) `$crate` — 引用定义宏的 crate；2) `pass_ident!` — 传递标识符参数；3) `proc_macro::Span`（过程宏）— 更精细的 hygiene 控制。应用场景：1) DSL（创建局部变量不污染作用域）；2) 内部迭代（`for` 循环宏不泄漏循环变量）；3) 内部状态（计数器、标志位）。这与 Scheme 的 hygienic macro（定义 hygienic macro 的 hygiene，Rust 类似）或 C 的 `#define`（完全无 hygiene，常见 bug 源）不同——Rust 的 declarative macro 默认 hygiene 是语言设计的安全特性。[来源: [Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)] · [来源: [The Little Book of Rust Macros](https://danielkeep.github.io/tlborm/book/)]
