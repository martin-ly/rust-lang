# 推理判定树图谱（Reasoning Judgment Tree Atlas）

> **EN**: Reasoning Judgment Tree Atlas
> **Summary**: Symptom → diagnostic question → root cause → fix strategy concept paths for compiler errors and runtime issues. 编译错误/运行时问题 → 判定问题 → 根因 → 修复策略的概念路径。
> **受众**: [研究者]
> **内容分级**: [元层]
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

---

## 一、使用说明

本图谱将常见编译错误与运行时问题抽象为**判定树**。每个节点提出一个诊断问题，最终叶子给出根因与应进入的权威概念页。本页不展开具体修复代码，只提供导航。

---

## 二、症状索引表

| 症状类别 | 典型报错/现象 | 入口判定树 |
|:---:|:---|:---|
| 借用冲突 | `cannot borrow as mutable` / `cannot borrow as immutable` | [借用冲突判定树](#31-借用冲突判定树) |
| 生命周期 | `lifetime may not live long enough` | [生命周期判定树](#32-生命周期判定树) |
| 类型不匹配 | `expected ... found ...` / trait bound unsatisfied | [类型不匹配判定树](#33-类型不匹配判定树) |
| 运行时 panic | `unwrap` panic / index out of bounds / deadlock | [运行时 panic 判定树](#34-运行时-panic-判定树) |
| unsafe 相关 | UB / Miri 报错 / soundness 质疑 | [unsafe 判定树](#35-unsafe-判定树) |

---

## 三、主要判定树

### 3.1 借用冲突判定树

```mermaid
flowchart TD
    B[借用冲突] --> Q1{是否同时存在 &T 和 &mut T？}
    Q1 -->|是| R1[根因：别名 XOR 可变性被破坏]
    Q1 -->|否| Q2{借用范围是否重叠？}
    Q2 -->|是| R2[根因：借用生命周期重叠]
    Q2 -->|否| Q3{是否在迭代器内部修改集合？}
    Q3 -->|是| R3[根因：集合迭代期间可变借用]
    Q3 -->|否| R4[根因：reborrow 或 split borrow 误用]
    R1 --> F1[[缩小可变借用范围 / 使用 Cell/RefCell/Mutex]]
    R2 --> F2[[引入新作用域 / clone 数据]]
    R3 --> F3[[先 collect 再处理 / 使用索引]]
    R4 --> F4[[见 Borrowing / Smart Pointers]]
```

### 3.2 生命周期判定树

```mermaid
flowchart TD
    L[生命周期错误] --> Q1{引用是否从函数返回？}
    Q1 -->|是| Q2{是否依赖局部变量？}
    Q2 -->|是| R1[根因：返回悬垂引用]
    Q2 -->|否| R2[根因：缺少显式生命周期参数]
    Q1 -->|否| Q3{是否跨 await 保存引用？}
    Q3 -->|是| R3[根因：async 状态机需要 'static 或自引用]
    Q3 -->|否| Q4{是否涉及 trait object 或 HRTB？}
    Q4 -->|是| R4[根因：高阶生命周期约束不足]
    Q4 -->|否| R5[根因：生命周期省略规则不适用]
    R1 --> F1[[返回 owned 数据 / 使用 Arc/Box]]
    R2 --> F2[[显式标注 'a / 使用生命周期省略规则]]
    R3 --> F3[[改用 owned 数据 / Pin]]
    R4 --> F4[[见 Lifetimes Advanced / HRTB]]
```

### 3.3 类型不匹配判定树

```mermaid
flowchart TD
    T[类型不匹配] --> Q1{是否缺少 trait bound？}
    Q1 -->|是| R1[根因：泛型参数未实现所需 trait]
    Q1 -->|否| Q2{是否混用了 &T 与 T？}
    Q2 -->|是| R2[根因：引用与值类型混淆]
    Q2 -->|否| Q3{是否使用了不同错误类型？}
    Q3 -->|是| R3[根因：Result 错误类型不统一]
    Q3 -->|否| Q4{是否 async fn 返回类型受限？}
    Q4 -->|是| R4[根因：impl Trait / RPITIT 边界]
    Q4 -->|否| R5[根因：类型推断失败或自定义类型未实现 trait]
    R1 --> F1[[添加 where T: Trait]]
    R2 --> F2[[解引用 / 借用 / 使用 Deref]]
    R3 --> F3[[使用 ? / map_err / 定义统一错误类型]]
    R4 --> F4[[见 Return Type Notation Preview / Async Advanced]]
```

### 3.4 运行时 panic 判定树

```mermaid
flowchart TD
    P[运行时 panic] --> Q1{是否由 unwrap/expect 触发？}
    Q1 -->|是| R1[根因：未处理的可恢复错误]
    Q1 -->|否| Q2{是否越界/切片越界？}
    Q2 -->|是| R2[根因：索引未验证]
    Q2 -->|否| Q3{是否 deadlock？}
    Q3 -->|是| R3[根因：锁顺序或 await 中持有锁]
    Q3 -->|否| Q4{是否跨 FFI 边界？}
    Q4 -->|是| R4[根因：ABI/生命周期/指针约定错误]
    Q4 -->|否| R5[根因：unsafe 导致 UB 或逻辑错误]
    R1 --> F1[[改用 ? / match / unwrap_or]]
    R2 --> F2[[使用 get / checked 方法]]
    R3 --> F3[[统一锁顺序 / 使用 try_lock / 避免跨 await 锁]]
    R4 --> F4[[见 FFI Advanced / Unsafe Rust]]
```

### 3.5 Unsafe 判定树

```mermaid
flowchart TD
    U[unsafe 问题] --> Q1{Miri 是否报 UB？}
    Q1 -->|是| Q2{是否涉及 raw pointer？}
    Q2 -->|是| R1[根因：别名规则或 provenance 违规]
    Q2 -->|否| R2[根因：未初始化内存/类型混淆]
    Q1 -->|否| Q3{是否在 safe API 中暴露 unsafe 不变式？}
    Q3 -->|是| R3[根因：safe 抽象违反 soundness]
    Q3 -->|否| R4[根因：unsafe 块范围过大或契约不清]
    R1 --> F1[[遵守 Stacked/Tree Borrows / 使用 NonNull]]
    R2 --> F2[[使用 MaybeUninit / 严格初始化]]
    R3 --> F3[[封装 invariant / Safety Tags]]
    R4 --> F4[[见 Unsafe Rust Patterns / Safety Tags Preview]]
```

---

## 四、按修复策略索引

| 修复策略 | 适用症状 | 权威概念页 |
|:---|:---|:---|
| 缩小借用范围 | 借用冲突、生命周期 | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md), [Lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) |
| 使用内部可变性 | 需要可变但只能拿到共享引用 | [Interior Mutability](../../02_intermediate/02_memory_management/08_interior_mutability.md) |
| 使用智能指针 | 共享所有权、堆分配、自引用 | [Smart Pointers](../../02_intermediate/02_memory_management/12_smart_pointers.md), [Pin and Unpin](../../03_advanced/01_async/06_pin_unpin.md) |
| 统一错误类型 | Result 链报错 | [Error Handling Deep Dive](../../02_intermediate/03_error_handling/16_error_handling_deep_dive.md) |
| 使用并发原语 | 跨线程数据竞争/死锁 | [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md), [Concurrency Patterns](../../03_advanced/00_concurrency/10_concurrency_patterns.md) |
| 形式化验证 | unsafe soundness 怀疑 | [Miri](../../04_formal/04_model_checking/31_miri.md), [Kani](../../04_formal/04_model_checking/32_kani.md), [RustBelt](../../04_formal/02_separation_logic/04_rustbelt.md) |

---

## 五、使用判定树的技巧

1. 从报错信息或现象定位症状类别。
2. 按顺序回答每个判定问题，避免同时修改多处代码。
3. 到达叶子节点后，先阅读推荐的权威概念页，再实施修复。
4. 若问题仍未解决，使用 [Miri](../../04_formal/04_model_checking/31_miri.md) 或 [Kani](../../04_formal/04_model_checking/32_kani.md) 进一步验证。

## 六、与相关元页的关系

- 需要按场景决策 → [场景决策树图谱](03_scenario_decision_tree_atlas.md)
- 需要查看示例/反例 → [示例与反例图谱](04_example_counterexample_atlas.md)
- 需要逻辑推理链 → [逻辑推理图谱](05_logical_reasoning_atlas.md)
- 需要概念定义 → [概念定义图谱](01_concept_definition_atlas.md)

---

> **内容分级**: [元层]
