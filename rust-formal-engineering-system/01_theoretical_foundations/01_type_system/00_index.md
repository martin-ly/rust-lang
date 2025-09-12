# 类型系统（Type System）索引

## 目的

- 梳理类型系统关键概念，为所有权/借用、泛型与抽象提供理论支撑。

## 核心主题

- 类型与多态：参数多态（泛型）、子类型、多态约束
- 代数数据类型（ADT）：和类型/积类型、模式匹配
- 生命周期与区域：作用域、借用、别名控制
- 效果与能力：错误、并发、不可变/可变能力
- 类型推断与一致性：Hindley–Milner 思想、约束求解

## 与 Rust 的关联

- 所有权与借用：通过生命周期与借用规则实现无 GC 的内存安全
- 泛型与 trait：零成本抽象与约束表达（`where`/关联类型）
- 枚举与匹配：以 ADT 建模状态机与协议
- `Send`/`Sync`：并发语义中的类型标记与跨线程安全

## 术语（Terminology）

- 类型（Type）/类型构造（Type Constructor）
- 多态（Parametric/Ad-Hoc/Subtyping）
- 代数数据类型（Sum/Product/Unit/Void）
- 生命周期（Lifetime）与借用（Borrow）
- 能力/效果（Capabilities/Effects）

## 形式化与证明（Formalization）

- 判断形式：`Γ ⊢ e : τ`（在环境 Γ 下，表达式 e 的类型为 τ）
- 进展与保持（Progress/Preservation）：保证类型安全的不出错性
- 类型化操作语义：小步/大步语义与带类型的规约关系
- 生命周期近似为区域（Region）内活性约束；借用规则对应别名与可变性互斥不变量

## 实践与样例（Practice）

- 泛型与抽象：参见 `crates/c04_generic/`
- 函数式与控制流：`crates/c03_control_fn/`
- 并发与异步：`crates/c05_threads/`、`crates/c06_async/`
- 分布式与一致性：`crates/c20_distributed/`

关联示例：在共识最小实现中，生命周期与借用规则可通过“作用域回调”降低 'static 约束：

```rust
// 详见 crates/c20_distributed/src/consensus_raft.rs
use c20_distributed::consensus_raft::{MinimalRaft, RaftNode, AppendEntriesReq, Term, LogIndex};

let mut raft: MinimalRaft<Vec<u8>> = MinimalRaft::new();
let mut buf = Vec::<Vec<u8>>::new();
{
    let mut apply = |e: &Vec<u8>| buf.push(e.clone());
    let mut scoped = raft.set_apply_scoped(&mut apply);
    let _ = scoped.handle_append_entries(AppendEntriesReq {
        term: Term(1), leader_id: "n1".into(), prev_log_index: LogIndex(0), prev_log_term: Term(0),
        entries: vec![b"x".to_vec()], leader_commit: LogIndex(1),
    });
}
assert_eq!(buf, vec![b"x".to_vec()]);
```

说明：通过在类型层面引入带生命周期的守卫对象，可在不放宽全局 'static 约束的前提下，安全地在局部作用域复用非 `'static` 闭包。

## 推荐阅读

- 语言层：`crates/c04_generic/`、`crates/c03_control_fn/`
- 并发层：`crates/c05_threads/`、`crates/c06_async/`

## 导航

- 返回理论基础：[`../00_index.md`](../00_index.md)
- 数学基础：[`../10_mathematical_foundations/00_index.md`](../10_mathematical_foundations/00_index.md)
- 宏系统：[`../08_macro_system/00_index.md`](../08_macro_system/00_index.md)
- 错误处理：[`../07_error_handling/00_index.md`](../07_error_handling/00_index.md)
