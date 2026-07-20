# 概览：类型系统（c02_type_system）

本模块聚焦 Rust 类型系统的理论与实践：类型定义、变体、代数数据类型、类型推断/安全、类型转换与包管理，以及与 Rust 1.89 的对齐。

---

## 目录导航

- 基础与定义
  - [type_define.md](./type_define.md)
  - [type_define_variant.md](./type_define_variant.md)
  - [type_variant.md](./type_variant.md)
  - [type_constructor/（源码）](../src/type_constructor/)

- 类型理论与范畴论视角
  - [type_type_theory.md](./type_type_theory.md)
  - [type_category_theory.md](./type_category_theory.md)
  - [type_HoTT.md](./type_HoTT.md)

- 推断与安全
  - [type_safety_inference.md](./type_safety_inference.md)
  - [type_inference/（源码）](../src/type_inference/)

- 类型转换与约束
  - [type_cast.md](./type_cast.md)
  - [type_down_up_cast.md](./type_down_up_cast.md)
  - [type_package.md](./type_package.md)

- 设计笔记与专题
  - [rust_type_design01.md](./rust_type_design01.md)
  - [rust_type_design02.md](./rust_type_design02.md)
  - [rust_type_design03.md](./rust_type_design03.md)
  - [rust_type_design04.md](./rust_type_design04.md)

- 与 Rust 1.89 的对齐
  - [rust_189_type_system_theory.md](./rust_189_type_system_theory.md)
  - [rust_189_alignment_summary.md](./rust_189_alignment_summary.md)

---

### 快速开始（示例）

1) 阅读基础：`type_define.md` → `type_variant.md`
2) 进阶理论：`type_type_theory.md` → `type_category_theory.md` → `type_HoTT.md`
3) 实战路径：查看 `src/` 中与类型构造、推断相关模块并运行示例/测试。

---

### 里程碑与后续规划

- 对齐 Rust 1.89 新特性影响范围，完善示例与边界条件验证。
- 增补“子类型/上升-下降转换”在安全边界内的更系统化案例。
- 与 `c04_generic` 的 GAT/HRTB 主题交叉互链。
