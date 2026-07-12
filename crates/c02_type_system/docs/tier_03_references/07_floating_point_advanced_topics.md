# 浮点数高级主题与 const fn 语义

> **EN**: Floating-Point Advanced Topics and const fn Semantics
> **Summary**: IEEE 754 semantics, NaN handling, special values, bit-pattern operations, numerical stability, and compile-time float capabilities in Rust. Migrated to the numerics authority.
>
> **适用 Rust 版本**: 1.92.0+
> **文档类型**: 重定向 stub

---

> **权威来源**: [concept/01_foundation/02_type_system/03_numerics.md](../../../../concept/01_foundation/02_type_system/03_numerics.md)

---

## 主题列表

- Rust 1.92.0 浮点数 const fn 能力
- NaN 语义、静默 NaN / 信号 NaN、payload
- 无穷大、有符号零、次正规数
- `to_bits` / `from_bits` 位模式操作
- 浮点数比较与近似相等
- 数值稳定性（Kahan 求和、避免灾难性抵消）
- 实战案例：金融计算、游戏引擎、科学计算、Softmax
