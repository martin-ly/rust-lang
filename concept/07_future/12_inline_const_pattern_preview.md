
### 10.4 边界测试：`const {}` 块在 pattern 中的使用（编译错误/未来特性）

```rust,ignore
fn main() {
    let x = 42;
    match x {
        // ❌ 编译错误: 当前稳定 Rust 不支持 const 块 in pattern
        // const { 40 + 2 } => println!("forty-two"),
        _ => println!("other"),
    }
    
    // 正确: 使用字面量或 const item
    const ANSWER: i32 = 42;
    match x {
        ANSWER => println!("forty-two"),
        _ => println!("other"),
    }
}
```

> **修正**: **Inline const patterns**（`const { expr }` in patterns）允许在 match arm 中直接写常量表达式：1) `match x { const { 1 + 1 } => ... }` — 编译期计算；2) 避免定义单独的 `const` item；3) 适用于复杂常量（如位运算、数组长度）。相关特性：1) **Inline const**（稳定于 1.79）：`let x: [u8; const { 1 + 1 }] = [0; 2]`；2) **Const blocks in patterns**（开发中）：将 inline const 扩展到 pattern 位置。使用场景：1) 复杂的 match 条件；2) 从其他常量派生的常量；3) 类型级计算的结果用于值级匹配。这与 C++ 的 `constexpr`（可在编译期计算，但不支持在 switch case 中使用复杂表达式）或 C 的 `case`（仅支持整型常量表达式）不同——Rust 的 `const {}` 更灵活，支持任意编译期可计算的 Rust 代码。[来源: [Inline Const RFC](https://rust-lang.github.io/rfcs/2920-inline-const.html)] · [来源: [Const Generics](https://rust-lang.github.io/rfcs/2000-const-generics.html)]
