# 组合软件工程有效性定理与证明

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)

---

## 公理与定义

**Def 1.1（模块组合）**:

设 $M_1, \ldots, M_n$ 为模块。组合 $C = M_1 \oplus \cdots \oplus M_n$ 满足：

- 各模块通过 `pub` 接口暴露，依赖通过 `use` 或 `mod` 建立
- 无循环依赖：$\mathrm{dep}(M_i)$ 的传递闭包不包含 $M_i$
- 类型环境：$\Gamma_C = \bigcup_i \Gamma_{M_i}$ 且无冲突

**Axiom CE0**：组合不引入新的全局可变状态；或新状态通过 `const`/`static` 正确初始化。

---

## 定理陈述与证明

### 定理 CE-T1（组合保持内存安全）

**陈述**：若各模块 $M_i$ 满足 [ownership_model](../../formal_methods/ownership_model.md) 定理 T2、T3（所有权唯一性、内存安全），则组合 $C = M_1 \oplus \cdots \oplus M_n$ 满足内存安全。

**证明思路**：

1. **归纳基**：单模块 $M_1$ 由前提满足 T2、T3。
2. **归纳步**：设 $C' = M_1 \oplus \cdots \oplus M_{n-1}$ 满足内存安全。添加 $M_n$ 时：
   - 模块边界：值通过函数参数/返回值传递，或通过 `pub` 结构体字段；所有权转移符合 T2。
   - 调用链：$M_n$ 调用 $C'$ 或反向；参数为值或引用，不违反借用规则。
   - 无新分配模式：$M_n$ 的 `Box`/`Vec` 等由所有权管理；释放由 RAII 保证。
3. **结论**：组合不引入悬垂、双重释放、泄漏；由 T2、T3 的归纳结构。

---

### 定理 CE-T2（组合保持数据竞争自由）

**陈述**：若各模块满足 [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) 定理 T1（数据竞争自由），且跨线程传递仅 Send 类型、共享仅 Sync 类型，则组合保持数据竞争自由。

**证明思路**：

1. **Send/Sync 结构性质**：若 $T$ 的所有字段为 Send，则 $T$ 为 Send；Sync 同理。组合不改变字段类型。
2. **跨模块边界**：`pub fn` 的签名若包含 `T: Send` 约束，则调用者保证传入 Send；组合后约束仍成立。
3. **borrow T1**：各模块内无数据竞争；跨模块调用在同一线程内为顺序，无交错；跨线程仅通过 Send 类型，无共享可变。
4. **结论**：组合保持数据竞争自由。

---

### 定理 CE-T3（组合保持类型安全）

**陈述**：若各模块良型，且 [type_system_foundations](../../type_theory/type_system_foundations.md) 进展性 T1、保持性 T2、类型安全 T3 成立，则组合程序良型且类型安全。

**证明思路**：

1. **模块良型**：各 $M_i$ 通过 `cargo check`；类型检查在模块边界通过 `pub` 接口进行。
2. **类型环境合并**：$\Gamma_C$ 为各模块导出类型与调用的并；无冲突因 `mod` 路径隔离。
3. **保持性**：跨模块调用时，实参类型与形参一致；返回值类型与调用处期望一致。由 type_system T2。
4. **结论**：组合后良型；由 T3 类型安全。

---

## 引理与推论

**引理 CE-L1（模块无环）**：若 $C = M_1 \oplus \cdots \oplus M_n$ 满足 Def 1.1，则依赖图 $G$ 为 DAG；$M_i \prec^* M_j \land M_j \prec^* M_i \Rightarrow \bot$。

*证明*：由 Def 1.1 无循环依赖；$\prec^*$ 为传递闭包，环存在则 $M_i \prec^* M_i$，矛盾。∎

**推论 CE-C1**：组合 CE-T1、CE-T2、CE-T3 可组合；若 $C$ 满足 CE-T1、CE-T2、CE-T3，则 $C$ 为 Safe 且良型。

*证明*：由各定理陈述；内存安全 + 数据竞争自由 + 类型安全 ⇒ Safe。∎

**推论 CE-C2（组合反例）**：若 $M_n$ 的 `pub` API 泄漏 `unsafe` 或违反借用规则，则 CE-T1 或 CE-T2 不成立；组合后可能 UB。

---

## 定理 CE-PAT1（模式组合 CE 保持）

**陈述**：设模式 $A$、$B$ 各自满足 CE-T1、CE-T2、CE-T3（作为独立模块）。若组合 $A \circ B$ 的接口满足 [03_integration_theory](03_integration_theory.md) IT-T1（跨模块所有权保持）、IT-T2（Send/Sync 传递）、IT-L1（生命周期约束），则 $A \circ B$ 保持 CE-T1、CE-T2、CE-T3。

**证明**：

1. **CE-T1**：$A$、$B$ 各自内存安全；组合时值/引用经 `pub fn` 边界传递，所有权转移符合 IT-T1；无新分配泄漏、无悬垂。由 ownership T2、T3。
2. **CE-T2**：$A$、$B$ 各自无数据竞争；跨模块调用顺序执行；跨线程仅 Send 类型，由 IT-T2。由 borrow T1、Send/Sync 结构性质。
3. **CE-T3**：$A$、$B$ 各自良型；跨模块实参/形参一致，由 IT-L1 与 type_system 保持性。∎

**推论 CE-PAT-C1**：Builder∘Factory、Decorator∘Strategy、Observer∘Command、Composite∘Visitor、Repository∘Service∘DTO 等组合，若满足 IT-T1/IT-T2/IT-L1，则保持 CE-T1–T3。

**组合推导示例（Builder + Factory）**：

- 接口：`Factory::create(&self) -> Builder`；`Builder::build(self) -> T`
- IT-T1：`create` 返回 Builder 所有权转移；`build` 消费 Builder 返回 T，所有权链完整
- IT-T2：若跨线程，Builder、T 需 `Send`；单线程则无约束
- IT-L1：无跨模块引用返回，不涉及
- **结论**：Builder∘Factory 保持 CE-T1–T3。∎

---

## 代码示例：模块组合

```rust
// crate::module_a
pub struct A { pub x: i32 }
impl A {
    pub fn new(x: i32) -> Self { Self { x } }
    pub fn get(&self) -> i32 { self.x }
}

// crate::module_b
pub struct B { pub a: A }
impl B {
    pub fn new(a: A) -> Self { Self { a } }
    pub fn run(&self) -> i32 { self.a.get() }
}

// 组合：main 使用 A 和 B
fn main() {
    let a = A::new(42);
    let b = B::new(a);  // a 所有权转移至 b
    assert_eq!(b.run(), 42);
}
```

**形式化对应**：`A`、`B` 为模块；`main` 组合两者。所有权：`a` 移入 `B::new`，符合 T2；无悬垂、无泄漏。

---

## 定理应用示例

| 定理 | 应用场景 |
| :--- | :--- |
| CE-T1 | 多 crate 项目：各 crate 内 Safe，组合后仍内存安全 |
| CE-T2 | 跨线程：只有 `Send` 类型跨线程传递，`Sync` 类型共享 |
| CE-T3 | 泛型模块：`fn f<T: Trait>(x: T)` 组合时类型检查在边界完成 |

---

## 验证方法

| 定理 | 验证手段 |
| :--- | :--- |
| CE-T1 | `cargo build` 无 unsafe 泄漏；`Valgrind`/`MIRI` 无内存错误 |
| CE-T2 | `cargo clippy` 检查 Send/Sync；无 `Rc` 跨线程 |
| CE-T3 | `cargo check` 通过；类型在 `pub` 边界一致 |

组合后运行测试套件；新增模块需补足单元测试。

---

## 组合有效性验证工作流（实质指南）

### 新增模块纳入组合时的检查清单

| 步骤 | 动作 | 验证 CE-T1/T2/T3 |
| :--- | :--- | :--- |
| 1 | 确认 `pub` 接口无 `unsafe` 泄漏 | CE-T1 |
| 2 | 跨线程类型检查 `Send`/`Sync` | CE-T2 |
| 3 | `cargo check` 通过 | CE-T3 |
| 4 | `cargo clippy` 无 Rc 跨线程、无双重借用 | CE-T2 |
| 5 | 可选：`MIRI` 检测未定义行为 | CE-T1 |
| 6 | 依赖图无环：`cargo tree` 检查 | Def 1.3 |

### 组合反例详解（何时定理不成立）

| 反例 | 违反定理 | 形式化说明 |
| :--- | :--- | :--- |
| `pub fn leak_raw(p: *mut T)` | CE-T1 | 泄漏裸指针违反 ownership 唯一性 |
| `pub fn spawn_rc(rc: Rc<T>)` | CE-T2 | Rc 非 Send，跨线程传递导致编译错误 |
| `pub fn bad_return<T>() -> T` | CE-T3 | 返回类型未约束，调用处类型推断失败 |
| `mod a { use super::b; } mod b { use super::a; }` | 引理 CE-L1 | 循环依赖，编译失败 |
| 泛型约束不一致 | CE-T3 | `impl<T: Trait> Service for T` 与 `Service<U>` 边界冲突 |

### 完整应用链示例：三层架构

**场景**：Web API 订单处理（表示层 + 业务层 + 数据层）。

```rust
// 层 1：DTO（跨边界）
#[derive(serde::Serialize, serde::Deserialize)]
pub struct PlaceOrderDto { pub items: Vec<ItemDto> }

// 层 2：Domain + Service（业务逻辑）
pub struct Order { id: u64, items: Vec<OrderItem> }
impl Order {
    fn from_dto(d: &PlaceOrderDto) -> Result<Self, String> { /* 校验 */ }
}

pub trait OrderRepository {
    fn save(&mut self, o: &Order) -> Result<(), String>;
}

pub struct OrderService<R: OrderRepository> { repo: R }
impl<R: OrderRepository> OrderService<R> {
    pub fn place_order(&mut self, dto: PlaceOrderDto) -> Result<u64, String> {
        let order = Order::from_dto(&dto)?;
        self.repo.save(&order)?;
        Ok(order.id)
    }
}

// 层 3：Controller（表示层，组合 Service）
pub struct OrderController<S: OrderServiceTrait> { service: S }
impl<S: OrderServiceTrait> OrderController<S> {
    pub fn handle(&mut self, req: PlaceOrderDto) -> Response {
        self.service.place_order(req).into()
    }
}
```

**CE-T1/T2/T3 验证**：各层 Safe；所有权沿 DTO→Order→Repository 传递；无共享可变；`cargo check` 通过即 CE-T3。

---

## 与 PROOF_INDEX 衔接

本部分定理纳入 [PROOF_INDEX](../../PROOF_INDEX.md)，按「组合软件工程」领域分类。
