# Compile Fail 验证报告 v3 (唯一文件名)

> 生成时间: 2026-05-24 19:16

## 摘要

| 状态 | 数量 |
|:---|:---|
| expected_fail | 462 |
| skipped | 124 |
| unexpected_pass | 1 |

## 问题代码块

| 文件 | 行号 | 状态 | 编译模式 | 预览 | 错误信息 |
|:---|:---|:---|:---|:---|:---|
| concept\03_advanced\06_pin_unpin.md | 696 | unexpected_pass | bin_direct | `use std::pin::Pin;  struct SelfRef ` | warning: unused import: `std::pin::Pin`  --> target\tmp\verify_compile |
