# C13 嵌入式系统 - 一页纸总结

> **用途**: 快速回顾核心概念与学习路径
> **完整文档**: [00_MASTER_INDEX](00_MASTER_INDEX.md)

---

## 核心概念

| 概念 | 说明 |
|---|---|
| `no_std` | 移除标准库依赖，使用 `core` 与 `alloc`（可选） |
| MMIO | 内存映射 I/O，通过原始指针访问外设寄存器 |
| UART | 通用异步收发器，嵌入式中最常见的串口通信 |
| 中断 | 外设通过中断向量表通知 CPU 处理异步事件 |
| HAL | 硬件抽象层，使用类型状态模式保证资源使用安全 |
| FFI | 与 C 代码/链接脚本/启动文件互操作 |

## 常见目标三元组

| 目标 | 场景 |
|---|---|
| `thumbv7m-none-eabi` | Cortex-M3，无操作系统，无硬浮点 |
| `thumbv7em-none-eabihf` | Cortex-M4/M7，硬浮点 |
| `x86_64-pc-windows-msvc` | Host 模拟编译与测试 |

## 学习路径

1. **入门**: `no_std` 环境 → 内存映射寄存器 → UART 驱动
2. **进阶**: 中断处理 → HAL 设计模式 → FFI 与 C 互操作
3. **高级**: RTIC 实时中断驱动 → Embassy 异步框架 → 裸机性能优化

## 速查命令

```bash
# Host 检查
cargo check -p c13_embedded

# 嵌入式目标（需安装 target）
cargo check -p c13_embedded --target thumbv7m-none-eabi --features embedded
```
---

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-28
