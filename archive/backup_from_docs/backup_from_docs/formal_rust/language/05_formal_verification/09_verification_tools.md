# 09 验证工具与方法

## 章节简介

本章系统梳理Rust主流形式化验证工具的原理、适用场景与工程集成，涵盖Prusti、Kani、Creusot等工具的自动化验证流程、CI/CD与IDE集成、典型用法与案例、工程意义与局限。

## 目录

1. 主流Rust验证工具原理与适用场景
2. 工具集成与工程实践
3. 典型用法与案例
4. 工程意义与局限
5. 参考文献

## 1. 主流Rust验证工具原理与适用场景

- **Prusti**：基于Viper中间语言，支持前置/后置条件、不变式、自动化验证，适合类型安全、内存安全、部分功能正确性。
- **Kani**：基于模型检查，适合嵌入式、并发、边界条件验证。
- **Creusot**：面向函数式验证，支持高阶函数、所有权、trait等高级特征。

> **适用场景**：
>
> - Prusti：类型安全、借用检查、前后置条件
> - Kani：边界条件、并发、嵌入式安全
> - Creusot：高阶函数、trait、复杂不变式

## 2. 工具集成与工程实践

- **CI/CD集成**：自动化验证纳入持续集成流水线，保障主干分支安全
- **IDE集成**：开发环境中实时反馈验证结果，提升开发效率
- **多工具协作**：Prusti+Kani+Creusot联合体体体覆盖不同验证需求

## 3. 典型用法与案例

- **Prusti**：

  ```rust
  use prusti_contracts::*;
  #[requires(n >= 0)]
  #[ensures(result >= n)]
  fn increment(n: i32) -> i32 { n + 1 }
  ```

- **Kani**：

  ```rust
  #[kani::proof]
  fn check_add() {
      let x: u8 = kani::any();
      let y: u8 = kani::any();
      assert!(x.wrapping_add(y) >= x);
  }
  ```

- **Creusot**：

  ```rust
  use creusot_contracts::*;
  #[logic]
  fn is_sorted(v: &Vec<i32>) -> bool { v.windows(2).all(|w| w[0] <= w[1]) }
  #[ensures(is_sorted(&result))]
  fn sorting_property(mut v: Vec<i32>) -> Vec<i32> { v.sort(); v }
  ```

## 4. 工程意义与局限

- **优势**：自动化验证提升代码安全、可靠性，便于大规模工程集成
- **局限**：工具覆盖面有限，复杂属性需手工补充，学习曲线存在

## 5. 参考文献

1. Prusti官方文档：<https://viperproject.github.io/prusti-dev/>
2. Kani官方文档：<https://model-checking.github.io/kani/>
3. Creusot官方文档：<https://creusot-rs.github.io/>

"

---
