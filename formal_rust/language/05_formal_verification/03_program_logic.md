# 03 程序逻辑与验证

## 章节简介

本章系统梳理Rust程序逻辑的形式化定义、核心定理与证明思路，涵盖Hoare逻辑、前后置条件、不变式、终止性、RAII与资源安全、Option/Result类型、借用规则等。通过形式化推理、代码示例与工程意义分析，帮助读者掌握Rust程序正确性的理论基础与验证方法。

## 目录

1. Hoare逻辑与前后置条件
2. 不变式与终止性
3. Rust中的程序逻辑建模
4. 形式化推理与代码示例
5. 工程意义与局限
6. 参考文献

## 1. Hoare逻辑与前后置条件

- **Hoare逻辑（Hoare Logic）**：用三元组 `{P} C {Q}` 形式化描述程序片段 C 的执行前置条件 P 和后置条件 Q。
- **前置条件**：程序执行前必须满足的断言。
- **后置条件**：程序执行后保证成立的断言。

> **形式化定义**：
>
> - `{P} C {Q}`：若在P成立时执行C，若C终止，则Q成立。
> - **部分正确性**：若C终止，则Q成立。
> - **全正确性**：C总会终止，且Q成立。

## 2. 不变式与终止性

- **循环不变式**：在循环每次迭代前后都成立的断言，是证明循环正确性的关键。
- **终止性**：程序最终会停止执行，不会陷入死循环。

> **定理**：
>
> - 若循环体保持不变式I，且每次迭代使某度量严格减小，则循环终止。

## 3. Rust中的程序逻辑建模

- **RAII与资源安全**：RAII模式下，资源的获取与释放可用不变式描述。
- **Option/Result类型**：通过类型系统表达部分正确性（如避免空指针、显式错误处理）。
- **不可变性与可变性**：借用规则可用前置/后置条件形式化。

> **建模示例**：
>
> - 资源释放不变式：`{资源已分配} drop {资源已释放}`
> - Option类型消除空指针：`{x: Option<T>} match x { Some(v) => ...; None => ... } {无未定义行为}`

## 4. 形式化推理与代码示例

```rust
fn safe_divide(a: i32, b: i32) -> Option<i32> {
    if b != 0 {
        Some(a / b)
    } else {
        None
    }
}
// 前置条件：b != 0
// 后置条件：返回 Some(a / b)
// 否则返回 None，避免除零错误
```

## 5. 工程意义与局限

- **优势**：提升代码健壮性、可验证性，便于自动化工具分析。
- **局限**：复杂程序的断言与不变式难以自动推导，形式化验证成本高。

## 6. 参考文献

1. Hoare, C. A. R. (1969). An axiomatic basis for computer programming. Communications of the ACM.
2. Dijkstra, E. W. (1975). Guarded commands, nondeterminacy and formal derivation of programs. Communications of the ACM.
3. Rust官方文档：Error Handling, Ownership, Borrowing.
