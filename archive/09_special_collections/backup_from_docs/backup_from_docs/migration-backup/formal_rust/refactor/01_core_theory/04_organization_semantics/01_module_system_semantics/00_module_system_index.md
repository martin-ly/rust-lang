# 4.1 模块系统语义索引

**文档编号**: RFTS-04-MSI  
**版本**: 1.0  
**最后更新**: 2025-01-27  
**状态**: 索引文档

---

## 文档结构

### 核心语义文档

1. **[模块定义语义](./01_module_definition_semantics.md)** - 模块声明和内联定义的语义模型
2. **[模块可见性语义](./02_module_visibility_semantics.md)** - 访问控制和可见性规则
3. **[模块路径语义](./03_module_path_semantics.md)** - 路径解析和名称查找算法
4. **[use语句语义](./04_use_statement_semantics.md)** - 导入机制和重导出语义

### 理论创新

- **模块层次理论**: 基于偏序关系的模块组织模型
- **可见性推断**: 自动可见性推断和检查算法
- **路径解析优化**: 高效的名称解析策略
- **模块封装性**: 形式化的封装不变式证明

### 跨层引用

- **[类型系统语义](../../01_foundation_semantics/01_type_system_semantics/)** - 类型在模块中的作用域
- **[生命周期语义](../../02_control_semantics/03_lifetime_semantics/)** - 跨模块生命周期管理
- **[宏系统语义](../../05_transformation_semantics/02_macro_semantics/)** - 宏的模块展开

---

*索引状态: 完成*  
*版本: 1.0*
