# 案例研究

> **生产级Rust项目深度分析**

---

## 目录说明

本目录包含对著名Rust开源库和框架的深度案例分析，从形式化角度分析其设计和实现。

---

## 专题案例

### 综合分析专题

位于 `comprehensive-analysis/case-studies/`

| 案例 | 内容 |
|:---|:---|
| Tokio运行时 | 调度器、IO驱动、性能分析 |
| Embassy嵌入式 | 无堆分配、实时性分析 |

### Actor专题

位于 `actor-specialty/case-studies/`

| 案例 | 内容 |
|:---|:---|
| Actix-web | 生产环境架构分析 |

---

## 案例分析维度

每个案例分析包含:

1. **项目概览** - 基本信息、定位
2. **架构分析** - 整体架构、关键组件
3. **形式化分析** - 安全定理、证明
4. **性能分析** - 基准测试、优化
5. **最佳实践** - 生产环境建议

---

## 分类索引

| 类别 | 案例 |
|:---|:---|
| 异步运行时 | Tokio, async-std |
| Web框架 | Actix-web, Axum |
| 嵌入式 | Embassy, RTIC |
| Actor系统 | Actix, Bastion |
| 数据库 | Diesel, SQLx |
| 序列化 | Serde, Rkyv |

---

**维护者**: Rust Case Study Team
