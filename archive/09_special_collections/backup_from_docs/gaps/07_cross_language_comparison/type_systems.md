# 类型系统比较：Rust 与主流语言

## 概述

比较所有权/借用、代数数据类型、类型推断、泛型系统（GAT、HKT 替代方案）、trait/接口/子类型。

## 维度

- 内存安全：线性/仿射类型、引用能力
- 泛型与约束：关联类型、常量泛型、特化与一致性
- 多态：参数/特设/子类型多态
- 类型推断：局部/全局、约束求解

## 额外维度（补充）

- 生命周期与别名模型：借用检查、不可变共享与独占可变
- 不安全边界：FFI/内存布局/别名不变量文档化
- 反射与运行时类型：TypeId/Any vs Java/Scala 反射

## 结论

- Rust 以所有权/借用替代 GC，结合强静态类型与约束系统；
- 在零成本抽象与可预测性能方面优势明显；
- 与 Haskell/Scala 的高阶类型能力可互补（以 GAT/宏系统弥合）。

---

## 对比矩阵（摘要）

| 维度 | Rust | Haskell | Scala | Java | C++ |
|---|---|---|---|---|---|
| 内存安全 | 所有权/借用（编译期） | GC | GC | GC | 手动/RAII |
| 泛型 | 单态化 + 关联类型/const 泛型 | 类型类/HKT | 泛型/HKT(部分) | 擦除泛型 | 模板（编译期） |
| 子类型 | 无子类型，多态 via trait | 无子类型 | 存在/协变逆变 | 存在/协变逆变 | 存在/复杂 |
| 类型推断 | 局部/约束求解 | 强 | 中 | 弱 | 弱 |
| 零成本抽象 | 强 | 强（但 GC） | 中 | 弱 | 强 |

### 运行时表达力补充

- Rust：`Any`/`TypeId` 提供受限反射；宏与生成在编译期完成
- Java/Scala：完整反射，加强元数据能力但有运行时成本

## 迁移陷阱与化解

- 广义子类型思维 → trait 组合与显式约束
- 宽接口 → 细粒度 trait 分解 + blanket impl
- 魔法隐式（Scala implicits） → 显式约束与 `where` 子句

## 示例：From/Into 与 TryFrom

```rust
#[derive(Debug)]
struct NonZero(u32);

impl TryFrom<u32> for NonZero {
    type Error = &'static str;
    fn try_from(v: u32) -> Result<Self, Self::Error> {
        if v == 0 { Err("zero not allowed") } else { Ok(NonZero(v)) }
    }
}
```

## 讨论要点

- Rust 通过 trait 与关联类型表达族关系，避免传统子类型的复杂性与成本。
- GATs 提升异步/借用关联返回类型表达力，缓解 HKT 缺失。
- Java 擦除泛型在运行时反射受限；C++ 模板具备强大元编程但错误信息复杂。

## 能力映射（补充）

- HKT 缺失替代：以 GATs + 关联类型 + trait 对象组合表达高阶约束；通过 `impl Trait` 与 RPIT 合成抽象。
- 线性/仿射约束：Rust 所有权即仿射语义；通过 `Drop`/`Copy` 辨别资源转移语义。
- 变体安全：`enum` 表达代数数据类型，借 `match` 穷尽检查提升总正确性。

## 典型迁移模式

1. 子类型层级 → trait 组合 + 新类型封装，提供 `Deref`/`From` 精准暴露。
2. Null/可空 → `Option<T>`；异常 → `Result<T,E>`；受检异常以类型建模错误域。
3. 共享可变 → 内部可变性（`Cell/RefCell`）或同步原语（`Mutex/RwLock`）。

## 示例：以 GAT 表达借用关联返回

```rust
trait Chunked {
    type Item<'a>
    where Self: 'a;
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}
```

要点：`Item<'a>` 将生命周期纳入关联类型，使借用返回在类型系统内可表达。

## 验证与工具

- creusot/prusti：契约与不变式验证
- kani：模型检查（有限状态空间）
- miri：解释器检查 UB 与别名模型

## 参考案例

- 从 Java Optional/异常 迁移到 `Option/Result` 的 API 设计指南
- 从 C++ 模板库迁移到 Rust 泛型 + trait bounds 的等价约束清单

## 迁移建议

- 将子类型设计改写为 trait 组合与新类型封装。
- 用枚举表达代数数据类型（避免继承层次）。
- 在边界以 `From/TryFrom` 提供安全转换。

## 参考

- Rust Reference; Scala DOT; System F; Hindley–Milner
