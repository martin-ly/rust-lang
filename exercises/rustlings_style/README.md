# Rustlings 风格交互式练习

> **难度**: 渐进式  
> **目标**: 通过修复编译错误的代码来学习 Rust

---

## 使用方法

1. 进入某一练习的目录：
   ```bash
   cd exercises/rustlings_style/ex01_borrow_fix
   ```

2. 尝试编译，观察错误信息：
   ```bash
   cargo check
   ```

3. 根据编译器提示修复 `src/lib.rs` 中的代码

4. 运行测试验证修复：
   ```bash
   cargo test
   ```

5. 修复成功后进入下一题

---

## 练习列表

| 编号 | 题目 | 考点 | 难度 |
| :--- | :--- | :--- | :--- |
| ex01 | borrow_fix | 借用检查器基本规则 | Easy |
| ex02 | mutable_borrow | 可变引用排他性 | Easy |
| ex03 | lifetime_elision | 生命周期省略与显式标注 | Easy |
| ex04 | string_ownership | String 与 &str 所有权 | Medium |
| ex05 | struct_lifetime | 结构体中的生命周期 | Medium |
| ex06 | trait_bound_fix | 特质约束缺失 | Easy |
| ex07 | generic_type_fix | 泛型参数使用错误 | Easy |
| ex08 | closure_capture | 闭包捕获方式 | Medium |
| ex09 | iterator_consumer | 迭代器消费规则 | Medium |
| ex10 | match_exhaustive | match 穷尽性检查 | Easy |

---

## 提示

- 编译器错误信息通常直接指出问题所在，仔细阅读 `help:` 和 `note:` 部分
- 如果卡住了，可以查看同目录下的 `solution.rs`（建议先自己尝试）
- 所有练习的目标都是让 `cargo test` 全部通过

---

## 与项目其他模块的关联

| 练习题 | 对应项目模块 |
| :--- | :--- |
| ex01–ex05 | `crates/c01_ownership_borrow_scope` |
| ex06–ex07 | `crates/c04_generic` |
| ex08–ex09 | `crates/c03_control_fn` |
| ex10 | `crates/c02_type_system` |
