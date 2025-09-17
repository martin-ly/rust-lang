# c01 所有权-借用-作用域：文档总览

本页汇总 `c01_ownership_borrow_scope` 的文档结构与阅读路径，帮助快速定位“所有权/借用/可变性/作用域”等主题材料。

## 导航与推荐阅读顺序

- 主题综述与对比：
  - [obs_vs_design.md](./obs_vs_design.md)
  - [obs_vs_function.md](./obs_vs_function.md)
  - [obs_rust_analysis.md](./obs_rust_analysis.md)
- 实战指南：
  - [PRACTICAL_GUIDE.md](./PRACTICAL_GUIDE.md)
- 概念脉络与对称性：
  - [rust_symmetry.md](./rust_symmetry.md)
- 细分主题速览：
  - 所有权与借用（ownership/borrow）见 `ownership/`、`move/`、`mutable/`
  - 作用域（scope）见 `scope/`
  - 变量与可变视图（variable/ viewX）见 `variable/`

## 目录结构（docs/）

### 根级文档

- [obs_rust_analysis.md](./obs_rust_analysis.md)
- [obs_vs_design.md](./obs_vs_design.md)
- [obs_vs_function.md](./obs_vs_function.md)
- [PRACTICAL_GUIDE.md](./PRACTICAL_GUIDE.md)
- [rust_symmetry.md](./rust_symmetry.md)
- [variable_analysis.md](./variable_analysis.md)

### ownership/

- `backup/` 历史材料：
  - ownership.md / ownership_transform.md / ownership_threads.md / ownership_whole_part.md / ownership_borrow_scope.md
- view01.md

### move/

- internal_mut_move.md
- move_ref_refmut_analysis.md
- partial_move.md
- rust_internalmut_move.md
- view01.md

### mutable/

- internal_mut.md
- internal_mutable.md
- mutable_model.md
- mutable_rust.md
- view01.md / view02.md / view03.md

### scope/

- `backup/static.md`
- scope_management_guide.md
- view01.md / view02.md

### variable/

- `backup/` 历史材料：category_variable.md / control_variable.md / 评价.md
- view01.md / view02.md / view03.md / view04.md

### memory/

- rust_balance.md / rust_balance01.md

## 使用建议

- 先读“综述/对比”，再进“实战指南”，最后按需查阅分主题细节与备份材料。
- 与 `examples/`、`src/` 对照练习，效果更佳。
