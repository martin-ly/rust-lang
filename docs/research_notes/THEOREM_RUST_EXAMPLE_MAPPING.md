# 定理与 Rust 示例映射表

> **创建日期**: 2026-02-26
> **最后更新**: 2026-02-27
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **用途**: 形式化定理 ↔ crates 示例双向映射，支撑「数学风格论证 + Rust 示例」衔接
> **状态**: ✅ 已完成 (Week 1 任务 P1-W1-T4) - 新增 Send/Sync/Pin/数据竞争/同步原语/生命周期映射
> **上位文档**: [CORE_THEOREMS_FULL_PROOFS](./CORE_THEOREMS_FULL_PROOFS.md)、[PROOF_INDEX](./PROOF_INDEX.md)

---

## 一、核心定理映射总览

| 定理ID | 定理名称 | 对应 crates | 关键示例 | 说明 |
| :--- | :--- | :--- | :--- | :--- |
| T-OW2 | 所有权唯一性 | c01_ownership_borrow_scope | moving02.rs, rust_192_features_demo.rs | 移动语义、唯一所有者 |
| T-OW3 | 内存安全框架 | c01_ownership_borrow_scope | 各 moving/borrow 示例 | 无悬垂、无双重释放 |
| T-OW6 | Send 安全 | c05_threads | thread_spawn_examples.rs | 跨线程转移所有权 |
| T-OW7 | Sync 安全 | c05_threads | arc_mutex_examples.rs | 多线程共享安全 |
| T-OW8 | Pin 不动性 | c06_async | pin_examples.rs | 自引用结构 |
| T-BR1 | 数据竞争自由 | c01_ownership_borrow_scope, c05_threads | borrow 示例、send_sync 示例 | 借用规则、Arc/Mutex |
| T-BR6 | 数据竞争定义 | c05_threads | data_race_examples.rs | 并发访问冲突 |
| T-BR7 | 同步原语 | c05_threads | mutex_rwlock_examples.rs | Mutex/RwLock/Atomic |
| T-TY1 | 进展性 | c02_type_system | type_equivalence_newtype_examples.rs | 良类型可求值 |
| T-TY2 | 保持性 | c02_type_system | 各类型示例 | 求值保持类型 |
| T-TY3 | 类型安全 | c02_type_system | never_type_control_flow.rs | 进展+保持 |
| T-LF1 | 生命周期包含 | c01, c02 | lifetimes_examples | outlives 关系 |
| T-LF2 | 引用有效性 | c01_ownership_borrow_scope | borrow 相关示例 | 无悬垂引用 |
| T-LF4 | 生命周期边界 | c01_ownership_borrow_scope | nll_examples.rs | NLL 非词法生命周期 |
| T-LF5 | 生命周期参数 | c02_type_system | generic_lifetimes_examples.rs | 泛型生命周期约束 |
| SEND-T1 | Send 安全 | c05_threads | 各 thread::spawn 示例 | 跨线程转移 |
| SYNC-T1 | Sync 安全 | c05_threads | Arc/Mutex 示例 | 多线程共享 |
| T-ASYNC1 | Future 安全性 | c06_async | futures_smoke.rs, async 示例 | 异步状态机 |
| T-PIN1 | Pin 不动性 | c06_async | pin 相关示例 | 自引用 Future |

---

## 二、按 crates 分类

### c01_ownership_borrow_scope

| 示例文件 | 对应定理 | 形式化概念 |
| :--- | :--- | :--- |
| moving02.rs | T-OW2 | 所有权转移、唯一性 |
| rust_192_features_demo.rs | T-OW2, T-BR1 | 移动、借用 |
| rust_190_features_examples.rs | T-OW2, T-OW3 | 所有权规则 1-8 |
| rust_189_features_examples.rs | T-BR1 | 借用规则 5-8 |

### c02_type_system

| 示例文件 | 对应定理 | 形式化概念 |
| :--- | :--- | :--- |
| type_equivalence_newtype_examples.rs | T-TY1, T-TY3 | 类型等价、Newtype |
| never_type_control_flow.rs | T-TY3 | 类型安全、! 类型 |
| rust_190_latest_features_demo.rs | T-TY2 | 类型保持 |
| lifetimes_examples.rs | T-LF1, T-LF2 | 生命周期、outlives |

### c05_threads

| 示例文件 | 对应定理 | 形式化概念 |
| :--- | :--- | :--- |
| 各 thread::spawn 示例 | SEND-T1 | Send trait |
| Arc/Mutex 示例 | SYNC-T1 | Sync trait |
| rust_193_features_demo.rs | SEND-T1, SYNC-T1 | 并发安全 |

### c06_async

| 示例文件 | 对应定理 | 形式化概念 |
| :--- | :--- | :--- |
| futures_smoke.rs | T-ASYNC1 | Future、Poll |
| pin 相关示例 | T-PIN1 | Pin、自引用 |
| async_state_machine 文档 | T6.1-T6.3 | 异步状态机 |

---

## 三、形式化文档引用规范

在 formal_methods、type_theory 文档中，每个 Def/Axiom/Theorem 应包含：

```markdown
### Rust 对应

- **示例**: [crates/c01_ownership_borrow_scope/examples/moving02.rs](../../../crates/c01_ownership_borrow_scope/examples/moving02.rs)
- **说明**: 移动后原变量不可用，体现 T-OW2 唯一性
```

---

## 四、05_guides 形式化引用

| 指南 | 应引用定理 | 示例 |
| :--- | :--- | :--- |
| ASYNC_PROGRAMMING_USAGE_GUIDE | T-ASYNC1, T6.1-T6.3, T-PIN1 | c06 示例 |
| THREADS_CONCURRENCY_USAGE_GUIDE | SEND-T1, SYNC-T1, T-BR1 | c05 示例 |
| UNSAFE_RUST_GUIDE | T-OW3, T-BR1 | c01 示例 |
| DESIGN_PATTERNS_USAGE_GUIDE | CE-T1-T3 | c09 示例 |
| MACRO_SYSTEM_USAGE_GUIDE | COH-T1, trait_system | c11 示例 |
| WASM_USAGE_GUIDE | T-ASYNC1, T6.1-T6.3 | c12 示例 |
| TROUBLESHOOTING_GUIDE | T-OW2, T-BR1, T-LF2 | 错误码映射 |
| PERFORMANCE_TUNING_GUIDE | T-OW3, SEND-T1, SYNC-T1 | c01, c05 |
| TESTING_COVERAGE_GUIDE | T-TY3, T-BR1 | 测试验证 |
| BEST_PRACTICES | T-OW2, T-BR1, T-TY3, SEND-T1, SYNC-T1 | 综合 |
| ADVANCED_TOPICS_DEEP_DIVE | T-OW2/T-OW3, advanced_types, SEND-T1/SYNC-T1 | 高级 |
| CLI_APPLICATIONS_GUIDE | T-OW2, T-BR1 | c07 |
| CROSS_MODULE_INTEGRATION_EXAMPLES | CE-T1-T3 | 跨模块 |
| EMBEDDED_RUST_GUIDE | T-OW3, T-BR1 | no_std |
| AI_RUST_ECOSYSTEM_GUIDE | T-OW2, T-TY3 | 张量、泛型 |

---

**维护者**: Rust 文档推进团队
**状态**: 持续补全中（P1-N1, P1-N2 任务）
