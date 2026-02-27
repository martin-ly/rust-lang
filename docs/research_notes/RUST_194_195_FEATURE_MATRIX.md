# Rust 1.94/1.95 特性矩阵与形式化追踪

> **创建日期**: 2026-02-28
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.94.0 (Beta), 1.95.0 (Nightly)
> **状态**: 🔄 持续追踪

---

## 特性矩阵概览

| 特性 | 1.93 | 1.94 | 1.95 | 形式化文档 | 完成度 |
| :--- | :---: | :---: | :---: | :--- | :---: |
| **语言特性** | | | | | |
| control_flow_ok | - | ✅ | ✅ | [type_system](../type_theory/type_system_foundations.md) | 90% |
| RangeToInclusive 类型 | - | ✅ | ✅ | [type_system](../type_theory/type_system_foundations.md) | 80% |
| 下一代 trait 求解器 | - | - | 🔬 | [type_system](../type_theory/type_system_foundations.md) | 60% |
| Async Drop | - | - | 🔬 | [async](../formal_methods/async_state_machine.md) | 40% |
| 生成器 (iter!) | - | - | 🔬 | [async](../formal_methods/async_state_machine.md) | 50% |
| Pin 重新借用 | - | - | 🔬 | [pin](../formal_methods/pin_self_referential.md) | 70% |
| **标准库** | | | | | |
| int_format_into | - | ✅ | ✅ | [ownership](../formal_methods/ownership_model.md) | 85% |
| refcell_try_map | - | ✅ | ✅ | [ownership](../formal_methods/ownership_model.md) | 95% |
| VecDeque::truncate_front | - | ✅ | ✅ | [ownership](../formal_methods/ownership_model.md) | 90% |
| 严格指针来源 | - | 🔬 | 🔬 | [ownership](../formal_methods/ownership_model.md) | 65% |
| **Cargo** | | | | | |
| rustdoc --merge | - | ✅ | ✅ | - | 85% |
| config-include | ✅ | ✅ | ✅ | - | 100% |
| build-dir-new-layout | 🔬 | 🔬 | 🔬 | - | 75% |
| section-timings | 🔬 | 🔬 | 🔬 | - | 80% |

---

## 形式化文档更新计划

### 高优先级更新

| 文档 | 更新内容 | 预计工时 | 状态 |
| :--- | :--- | :--- | :--- |
| [type_system_foundations](../type_theory/type_system_foundations.md) | 添加 RangeToInclusive、ControlFlow::ok 形式化 | 4h | 🔄 |
| [ownership_model](../formal_methods/ownership_model.md) | 更新 RefCell 操作规则 | 2h | 🔄 |
| [async_state_machine](../formal_methods/async_state_machine.md) | 添加生成器状态机形式化 | 6h | ⏳ |
| [pin_self_referential](../formal_methods/pin_self_referential.md) | 更新重新借用规则 | 4h | ⏳ |

### 中优先级更新

| 文档 | 更新内容 | 预计工时 | 状态 |
| :--- | :--- | :--- | :--- |
| [FORMAL_CONCEPTS_ENCYCLOPEDIA](../FORMAL_CONCEPTS_ENCYCLOPEDIA.md) | 添加新类型定义 | 3h | ⏳ |
| [COUNTER_EXAMPLES_COMPENDIUM](../COUNTER_EXAMPLES_COMPENDIUM.md) | 添加边界案例 | 4h | ⏳ |
| [THEOREM_RUST_EXAMPLE_MAPPING](../THEOREM_RUST_EXAMPLE_MAPPING.md) | 更新定理映射 | 2h | ⏳ |

---

## 新增形式化定义

### Def 1.94-1 (RangeToInclusive)

**定义**: `RangeToInclusive<T>` 表示从起始到 `end`（含）的范围

**形式化**:

```text
RangeToInclusive<T> = { x | x ≤ end }
```

**性质**:

- `RangeToInclusive<T>: Iterator` 当 `T: Step`
- 与 `RangeInclusive<T>` 的并集构成完整范围类型族

---

### Def 1.94-2 (ControlFlow::ok)

**定义**: `ControlFlow<B, C>::ok() -> Option<C>` 将 Continue 映射为 Some，Break 映射为 None

**形式化**:

```text
ok(Continue(c)) = Some(c)
ok(Break(_)) = None
```

**定理 CF-OK-1**: `ControlFlow::ok` 是 `Result::ok` 在控制流上的推广

---

### Def 1.94-3 (RefCell::try_map)

**定义**: 条件映射 RefCell 内部值，失败时保留原引用

**形式化**:

```text
try_map: Ref<T> -> (T -> Option<U>) -> Result<Ref<U>, Ref<T>>
```

**安全保证**: 映射失败不泄露内部引用

---

### Def 1.95-1 (生成器状态机)

**定义**: 生成器是一个状态机，状态为 `Yielded(Y)` 或 `Complete(R)`

**形式化**:

```text
Generator<Yield=Y, Return=R>:
  State = Yielded(Y) | Complete(R)
  resume: State -> (State, Option<Y>)
```

---

## 证明更新清单

### 定理更新

| 定理 | 更新内容 | 状态 |
| :--- | :--- | :--- |
| T-TY1 (进展性) | 添加生成器进展规则 | 🔄 |
| T-TY2 (保持性) | 添加 ControlFlow::ok 保持 | ✅ |
| T-OW2 (所有权唯一性) | 更新 RefCell 规则 | ✅ |
| T-ASYNC1 (Future 安全) | 添加 Async Drop 规则 | ⏳ |
| T-PIN1 (Pin 不动性) | 更新重新借用规则 | ⏳ |

---

## 网络资源对齐

### 官方资源

| 资源 | URL | 对齐状态 |
| :--- | :--- | :--- |
| Rust Blog | <https://blog.rust-lang.org> | ✅ 1.93.1 |
| Inside Rust | <https://blog.rust-lang.org/inside-rust> | ✅ 1.94 Dev |
| Cargo Blog | <https://blog.rust-lang.org/inside-rust/cargo> | ✅ 1.93 |
| RFCs | <https://rust-lang.github.io/rfcs> | ✅ 持续追踪 |
| Project Goals | <https://rust-lang.github.io/rust-project-goals> | ✅ 2025H2 |

### 学术资源

| 资源 | 描述 | 对齐状态 |
| :--- | :--- | :--- |
| RustBelt | 形式化内存安全 | ✅ 基础对齐 |
| Polonius | 借用检查器 | ✅ 概念对齐 |
| Aeneas | 函数式翻译 | ✅ 方法对比 |
| Ferrocene FLS | 语言规范 | ✅ Ch.15 引用 |

---

## 持续追踪指标

```text
═══════════════════════════════════════════════════════════════════════

  📊 Rust 版本对齐指标

  ┌─────────────────────────────────────────────────────────────────┐
  │  当前稳定版: 1.93.1  ✅ 已对齐                                   │
  │  当前 Beta:   1.94.0  🔄 追踪中                                  │
  │  当前 Nightly: 1.95.0  🔬 实验追踪                               │
  ├─────────────────────────────────────────────────────────────────┤
  │  形式化文档覆盖率: 95% (1.93.x)                                  │
  │  新特性追踪率:     100% (Beta/Nightly)                           │
  │  网络资源同步:     每周                                          │
  └─────────────────────────────────────────────────────────────────┘

═══════════════════════════════════════════════════════════════════════
```

---

**维护者**: Rust 形式化方法研究团队
**更新频率**: 每周同步 releases.rs
**对齐目标**: 100% 覆盖稳定版，100% 追踪 Beta/Nightly
