# c13 嵌入式系统 - 文档指南

> **文档治理**: 本 crate 的通用模板文档（FAQ / Glossary / MIND_MAP / ONE_PAGE_SUMMARY / PENDING_ITEMS / MASTER_INDEX）已集中到 [`crates/common/docs/`](../../common/docs)。
> 概念解释的权威来源为 [`concept/`](../../../../concept/) 对应主题。
>

## 模块定位

本 crate 提供 Rust 裸机嵌入式系统学习模块，涵盖 `no_std` 编程、内存映射寄存器、UART 驱动、中断处理、HAL 设计模式、FFI 与 C 互操作、以及 Embassy / RTIC 异步嵌入式框架。

## 快速导航

- [裸机基础指南](bare_metal_guide.md)
- [build-std 与自定义目标](build_std_guide.md)
- [embedded-hal 1.0 迁移指南](embedded_hal_1_0_migration.md)
- [一页纸总结](one_page_summary.md)
- [完整索引](00_master_index.md)

## 编译说明

- **Host 目标** (`x86_64-pc-windows-msvc`): 使用模拟代码演示概念，`cargo check` 可正常通过
- **嵌入式目标** (`thumbv7m-none-eabi` 等): 启用 `embedded` feature，使用真实硬件抽象层

## 运行示例

```bash
# Host 上检查编译
cargo check -p c13_embedded

# 运行演示程序
cargo run -p c13_embedded --bin embedded_demo
```

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-06-28
**状态**: ✅ 基础文档补齐
