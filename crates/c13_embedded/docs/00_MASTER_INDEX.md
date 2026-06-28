# c13 嵌入式系统 - 主索引

> **版本**: 1.0
> **适用版本**: Rust 1.96.0+
> **最后更新**: 2026-06-28

---

## 目录

- [c13 嵌入式系统 - 文档指南](README.md)
- [一页纸总结](ONE_PAGE_SUMMARY.md)
- [裸机基础指南](BARE_METAL_GUIDE.md)
- [build-std 与自定义目标](BUILD_STD_GUIDE.md)
- [embedded-hal 1.0 迁移指南](EMBEDDED_HAL_1_0_MIGRATION.md)

## 按主题浏览

### 基础

- [裸机基础指南](BARE_METAL_GUIDE.md) - `no_std`、启动流程、链接脚本
- [build-std 与自定义目标](BUILD_STD_GUIDE.md) - 自定义 target 与 `build-std`

### 硬件抽象

- [embedded-hal 1.0 迁移指南](EMBEDDED_HAL_1_0_MIGRATION.md) - HAL trait 与迁移实践

### 代码模块

- `src/bare_metal_basics.rs`
- `src/memory_mapped_registers.rs`
- `src/uart_driver.rs`
- `src/interrupt_handling.rs`
- `src/hal_design_patterns.rs`
- `src/ffi_c_interop.rs`
- `src/rtic_framework.rs`
- `src/embassy_framework.rs`

## 编译与测试

```bash
# Host 检查
cargo check -p c13_embedded

# 运行演示
cargo run -p c13_embedded --bin embedded_demo

# 嵌入式目标
cargo check -p c13_embedded --target thumbv7m-none-eabi --features embedded
```

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-28
**状态**: ✅ 基础索引
