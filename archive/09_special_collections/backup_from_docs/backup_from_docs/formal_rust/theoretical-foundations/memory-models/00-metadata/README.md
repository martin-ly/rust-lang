# 内存管理模块工程案例说明

## 案例目录

- example_alloc_free.rs      —— 内存分配与释放
- example_dangling_pointer.rs —— 悬垂指针检测与防护
- example_memory_leak.rs     —— 内存泄漏检测与可达性
- example_manual_vs_gc.rs    —— 手动管理与垃圾回收对比

## 理论映射

- 每个案例均与[内存管理模型理论](../01_formal_memory_model.md)的相关定义、定理直接对应。
- 例如：example_dangling_pointer.rs 对应“悬垂指针”与“无悬垂指针”定理。
- example_memory_leak.rs 对应“内存泄漏检测”定理。

## 编译与验证

- 所有案例可直接用 `rustc` 编译。
- 推荐配合自动化测试脚本批量验证（见 tools/ 目录）。
- 案例代码如有编译错误或理论不符，请在此文档下方记录。

## 后续补全提示

- 如需补充新案例，请按“理论映射-代码-验证”三段式补全。
- 案例与理论的交叉借用建议在代码注释和本说明中同步补全。

> 本文档为标准化模板，后续可根据实际案例补充详细说明与交叉借用。
