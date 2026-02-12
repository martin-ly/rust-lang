# 反模式与边界

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: 层次推进扩展

---

## 宗旨

将设计模式反例、反模式与形式化边界衔接，提供**实质内容**：形式化对应、与安全边界关系、规避策略、与 FORMAL_PROOF_SYSTEM_GUIDE 反例索引的衔接。

---

## 一、反模式与安全边界

### 1.1 形式化定义

**Def AP1（反模式）**：违反设计模式不变式或 Rust 安全规则的实现；$\mathit{SafeB}(P) = \mathrm{Inexpr}$ 或违反 [ownership_model](../../formal_methods/ownership_model.md)、[borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) 规则。

**Axiom AP1**：反模式导致 UB、数据竞争、或逻辑错误；与 [safe_unsafe_matrix](05_boundary_system/safe_unsafe_matrix.md) SBM-T2、SBM-L2 衔接。

### 1.2 反模式分类

| 分类 | 边界 | 示例 |
| :--- | :--- | :--- |
| **所有权反模式** | 违反 ownership | 使用已移动值、循环引用泄漏 |
| **借用反模式** | 违反 borrow | 双重可变借用、迭代中修改集合 |
| **并发反模式** | 违反 Send/Sync | Rc 跨线程、共享可变无同步 |
| **设计模式反模式** | 违反模式不变式 | 违反 Builder 必填、Singleton 多实例 |

---

## 二、13 反例索引（与 FORMAL_PROOF_SYSTEM_GUIDE 衔接）

| 模式 | 反例 | 后果 | 规避 |
| :--- | :--- | :--- | :--- |
| Singleton | 全局可变未同步 | 数据竞争 | OnceLock、LazyLock |
| Observer | 共享可变无 Mutex | 数据竞争 | channel、Arc\<Mutex> |
| Composite | 循环引用 | 所有权无法表达 | 避免自引用、用 Weak |
| Builder | build 前必填未设 | 运行时错误 | 类型状态、ok_or |
| Memento | 恢复非法状态 | 不变式违反 | 校验、Clone 约束 |
| Iterator | 迭代中修改集合 | 借用冲突 | 借用规则 1 |
| Prototype | Clone 浅拷贝共享 | 隐式耦合 | 深拷贝、显式 |
| Flyweight | 跨线程用 Rc | 编译错误 | Arc |
| Mediator | 循环引用 | 泄漏 | Weak 打破环 |
| Chain | 链成环 | 无限循环 | 无环约束 |
| 其他 | 见 FORMAL_PROOF_SYSTEM_GUIDE | - | - |

**完整反例**：见 [FORMAL_PROOF_SYSTEM_GUIDE](../../FORMAL_PROOF_SYSTEM_GUIDE.md#设计模式反例)。

---

## 三、常见反模式详解

### 3.1 所有权反模式

| 反模式 | 形式化 | 规避 |
| :--- | :--- | :--- |
| 使用已移动值 | 违反 ownership 规则 2 | 移动后不再使用 |
| 循环 Rc | $\text{strong\_count} \geq 1$ 永不归零 | 用 Weak 打破环 |
| 过早 drop | 违反 outlives | 显式生命周期 |

### 3.2 借用反模式

| 反模式 | 形式化 | 规避 |
| :--- | :--- | :--- |
| 双重可变借用 | 违反 borrow 规则 1 | 作用域分离 |
| 迭代中修改 | 违反 borrow 规则 1 | 先收集再修改 |
| 返回局部引用 | 违反 lifetime 规则 | 返回 owned 或 'a 引用 |

### 3.3 设计模式反模式

| 反模式 | 形式化 | 规避 |
| :--- | :--- | :--- |
| 单产品用 Abstract Factory | 过度设计 | Factory Method |
| 简单调用用 Chain | 不必要的链 | 直接调用 |
| 无共享用 Flyweight | 无收益 | 普通创建 |
| 顺序操作用 Mediator | 过度解耦 | 直接调用 |

---

## 四、反模式与三维边界

| 反模式 | 安全边界 | 支持边界 | 表达边界 |
| :--- | :--- | :--- | :--- |
| static mut 多线程 | Inexpr | - | - |
| Rc 跨线程 | 编译错误 | - | - |
| 双重可变借用 | 编译错误 | - | - |
| 误选模式 | - | - | 过度设计 |

---

## 五、与 05_boundary_system 衔接

- [safe_unsafe_matrix](05_boundary_system/safe_unsafe_matrix.md)：SBM-L2 反模式边界
- [02_workflow 03_semantic_boundary_map](02_workflow_safe_complete_models/03_semantic_boundary_map.md)：反模式误选表
- [01_design_patterns_formal](01_design_patterns_formal/README.md)：各模式反例

---

## 六、引用

- [FORMAL_PROOF_SYSTEM_GUIDE](../../FORMAL_PROOF_SYSTEM_GUIDE.md#设计模式反例)
- [rust-unofficial/patterns](https://rust-unofficial.github.io/patterns/) Anti-patterns
- [safe_unsafe_matrix](05_boundary_system/safe_unsafe_matrix.md)
