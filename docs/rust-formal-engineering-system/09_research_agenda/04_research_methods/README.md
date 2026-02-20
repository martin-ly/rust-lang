# 研究方法

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> 内容已整合至： [research_methodology.md](../../../../research_notes/research_methodology.md)

[返回主索引](../../00_master_index.md)

---

## 研究方法概述

### 形式化方法研究流程

```
问题定义
    ↓
形式化建模（数学定义）
    ↓
定理陈述
    ↓
证明构造
    ↓
证明验证（人工/工具）
    ↓
文档化
    ↓
代码实现与验证
```

### 研究笔记结构

```markdown
# 研究笔记模板

## 问题陈述
- 研究什么问题
- 为什么重要

## 形式化定义
- 数学符号定义
- 类型/状态定义

## 定理与证明
- 定理陈述
- 证明步骤
- 证明验证

## 实现考虑
- Rust 实现映射
- 边界条件

## 开放问题
- 未解决的疑问
- 进一步研究方向
```

### 证明验证工具

```rust
// 形式化验证工具链

// 1. MIRI：检测未定义行为
cargo miri test

// 2. Kani：模型检查
#[kani::proof]
fn verify_property() {
    let x: u32 = kani::any();
    kani::assume(x < 100);
    assert!(x * 2 < 200);
}

// 3. Prusti：基于契约的验证
#[requires(x > 0)]
#[ensures(result > x)]
fn double(x: i32) -> i32 {
    x * 2
}
```

## 形式化方法

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 形式化方法概述 | 形式化验证基础理论 | [../../../../../research_notes/formal_methods/README.md](../../../../../research_notes/formal_methods/README.md) |
| 形式化验证指南 | 完整验证流程 | [../../../../../research_notes/FORMAL_VERIFICATION_GUIDE.md](../../../../../research_notes/FORMAL_VERIFICATION_GUIDE.md) |
| 证明系统指南 | 形式化证明方法 | [../../../../../research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md](../../../../../research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md) |
| 所有权模型形式化 | 所有权系统数学定义 | [../../../../../research_notes/formal_methods/ownership_model.md](../../../../../research_notes/formal_methods/ownership_model.md) |

## 相关研究笔记

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 研究方法论 | 研究方法指南 | [../../../../../research_notes/research_methodology.md](../../../../../research_notes/research_methodology.md) |
| 形式化验证工具 | 工具使用指南 | [../../../../../research_notes/TOOLS_GUIDE.md](../../../../../research_notes/TOOLS_GUIDE.md) |
| 证明索引 | 形式化证明集合 | [../../../../../research_notes/PROOF_INDEX.md](../../../../../research_notes/PROOF_INDEX.md) |
| 研究路线图 | 长期研究规划 | [../../../../../research_notes/RESEARCH_ROADMAP.md](../../../../../research_notes/RESEARCH_ROADMAP.md) |
