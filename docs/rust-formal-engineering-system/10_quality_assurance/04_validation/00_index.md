# 验证（Validation）索引

## 📊 目录

- [验证（Validation）索引](#验证validation索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [验证类型](#验证类型)
  - [核心概念](#核心概念)
  - [工具链](#工具链)
  - [实践与样例](#实践与样例)
  - [相关索引](#相关索引)
  - [导航](#导航)

## 目的

- 介绍 Rust 项目中的各种验证技术与工具。
- 提供静态分析、动态分析、形式化验证的实践指南。

## 验证类型

- 静态分析：编译时程序分析，如 `clippy`、`rustc` 警告
- 动态分析：运行时程序分析，如 `miri`、ASAN、TSAN
- 形式化验证：数学方法证明程序正确性，如 Kani、Prusti
- 属性测试：基于属性的随机测试，如 `proptest`
- 模糊测试：自动生成输入进行测试，如 `cargo-fuzz`

## 核心概念

- 类型安全：编译时保证类型正确性
- 内存安全：防止内存泄漏、悬垂指针、缓冲区溢出
- 并发安全：防止数据竞争、死锁
- 功能正确性：程序行为符合规格说明

## 工具链

- 静态分析：`clippy`、`rustc`、`cargo udeps`
- 动态分析：`miri`、ASAN、TSAN、LSAN
- 形式化验证：Kani、Prusti、Creusot
- 属性测试：`proptest`、`quickcheck`
- 模糊测试：`cargo-fuzz`、AFL++

## 实践与样例

- 静态分析：参见 [crates/c03_control_fn](../../../crates/c03_control_fn/)
- 动态分析：[crates/c05_threads](../../../crates/c05_threads/)
- 形式化验证：[crates/c04_generic](../../../crates/c04_generic/)

## 相关索引

- 测试：[`../05_testing/00_index.md`](../05_testing/00_index.md)
- 工具链生态：[`../../06_toolchain_ecosystem/00_index.md`](../../06_toolchain_ecosystem/00_index.md)
- 理论基础（形式化验证）：[`../../01_theoretical_foundations/09_formal_verification/00_index.md`](../../01_theoretical_foundations/09_formal_verification/00_index.md)

## 导航

- 返回质量保障：[`../00_index.md`](../00_index.md)
- 测试：[`../05_testing/00_index.md`](../05_testing/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
