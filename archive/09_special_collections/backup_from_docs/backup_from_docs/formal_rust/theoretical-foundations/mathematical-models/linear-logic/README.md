# 所有权模块工程案例说明

## 案例目录

- example_move_semantics.rs  —— 所有权转移与移动语义
- example_borrowing.rs      —— 借用规则与生命周期
- example_mut_borrow.rs     —— 可变借用与借用冲突
- example_dangling_ref.rs   —— 悬垂借用与借用检查

## 理论映射

- 每个案例均与[所有权系统形式化理论](../01_formal_ownership_system.md)的相关定义、定理直接对应。
- 例如：example_move_semantics.rs 对应“所有权转移”与“所有权唯一性”定理。
- example_borrowing.rs 对应“借用规则”与“借用安全性”定理。

## 编译与验证

- 所有案例可直接用 `rustc` 编译。
- 推荐配合自动化测试脚本批量验证（见 tools/ 目录）。
- 案例代码如有编译错误或理论不符，请在此文档下方记录。

## 后续补全提示

- 如需补充新案例，请按“理论映射-代码-验证”三段式补全。
- 案例与理论的交叉借用建议在代码注释和本说明中同步补全。

> 本文档为标准化模板，后续可根据实际案例补充详细说明与交叉借用。

## 生命周期相关案例

- example_lifetime_basic.rs  —— 生命周期基础约束
- example_lifetime_fn.rs     —— 函数生命周期标注
- example_lifetime_struct.rs —— 结构体生命周期标注
- example_lifetime_static.rs —— 静态生命周期

- 所有案例均与[生命周期与作用域分析](../02_lifetime_and_scope.md)的相关定义、定理直接对应。
- 如需补充新案例，请在此处登记并注明理论映射。
