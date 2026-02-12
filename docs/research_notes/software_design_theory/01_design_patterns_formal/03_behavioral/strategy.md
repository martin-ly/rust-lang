# Strategy 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 行为型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（Strategy 结构）**:

设 $C$ 为上下文类型，$S$ 为策略类型。Strategy 满足：

- $C$ 持有 $S$：$C \supset S$（$C$ 包含 $S$ 作为字段）
- $\mathit{execute}(c) = c.\mathit{strategy}.\mathit{algorithm}(c.\mathit{data})$
- 策略可替换：$S$ 实现 trait $\mathcal{T}$，不同 impl 可互换

**Axiom SR1**：策略接口一致；不同策略对相同输入类型产生相同输出类型。

**Axiom SR2**：上下文持有策略的所有权或引用；无循环依赖。

**定理 SR-T1**：trait 定义策略接口；`impl Trait` 或 `dyn Trait` 实现多态；由 [trait_system_formalization](../../../type_theory/trait_system_formalization.md) 解析正确性。

**定理 SR-T2**：策略调用时借用规则：`&self` 不可变调用策略；`&mut self` 可变时仍满足互斥。由 [borrow_checker_proof](../../../formal_methods/borrow_checker_proof.md)。

**推论 SR-C1**：Strategy 为纯 Safe；trait 多态策略，无 `unsafe`。由 SR-T1、SR-T2 及 [safe_unsafe_matrix](../../05_boundary_system/safe_unsafe_matrix.md) SBM-T1。

---

## Rust 实现与代码示例

```rust
trait Strategy {
    fn execute(&self, data: &[i32]) -> i32;
}

struct SumStrategy;
impl Strategy for SumStrategy {
    fn execute(&self, data: &[i32]) -> i32 { data.iter().sum() }
}

struct MaxStrategy;
impl Strategy for MaxStrategy {
    fn execute(&self, data: &[i32]) -> i32 { *data.iter().max().unwrap_or(&0) }
}

struct Context<S: Strategy> {
    strategy: S,
    data: Vec<i32>,
}

impl<S: Strategy> Context<S> {
    fn new(strategy: S, data: Vec<i32>) -> Self {
        Self { strategy, data }
    }
    fn run(&self) -> i32 {
        self.strategy.execute(&self.data)
    }
}

// 使用：编译期多态
let ctx = Context::new(SumStrategy, vec![1, 2, 3]);
assert_eq!(ctx.run(), 6);

// 或运行时多态
let ctx: Context<Box<dyn Strategy>> = Context::new(
    Box::new(MaxStrategy),
    vec![1, 2, 3],
);
assert_eq!(ctx.run(), 3);
```

**形式化对应**：`Context<S>` 即 $C \supset S$；`run` 即 $\mathit{execute}$；`Strategy` trait 为策略接口。

---

## 证明思路

1. **类型安全**：`S: Strategy` 约束保证 `execute` 存在且签名一致；由 trait_system 解析。
2. **所有权**：`Context` 拥有 `strategy` 和 `data`；`run(&self)`  borrow 两者，无移出。由 ownership T2。

---

## 与 GoF 对比

GoF 中 Strategy 为接口 + 多实现；Rust 用 trait + impl 等价表达，且无虚函数开销（泛型单态化时）。

---

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| 排序/搜索算法 | 不同策略可互换 |
| 压缩/序列化 | 多种格式策略 |
| 验证规则 | 不同校验策略 |
| 渲染/布局 | 不同渲染后端 |

---

## 完整场景示例：压缩格式策略（零成本抽象）

**场景**：数据导出支持 gzip、zstd 多种压缩；运行时选择格式。

```rust
trait CompressStrategy {
    fn compress(&self, data: &[u8]) -> Vec<u8>;
}

struct GzipStrategy;
impl CompressStrategy for GzipStrategy {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        // 实际：use flate2::Compression; flate2::write::GzEncoder::new(...)
        data.to_vec()
    }
}

struct ZstdStrategy;
impl CompressStrategy for ZstdStrategy {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        // 实际：zstd::encode_all(data, 3)
        data.to_vec()
    }
}

struct Exporter<S: CompressStrategy> {
    strategy: S,
}

impl<S: CompressStrategy> Exporter<S> {
    fn new(strategy: S) -> Self { Self { strategy } }
    fn export(&self, data: &[u8]) -> Vec<u8> {
        self.strategy.compress(data)
    }
}

// 编译期多态：无虚调用开销
let ex = Exporter::new(GzipStrategy);
let _ = ex.export(b"hello");
```

**形式化对应**：`Exporter<S>` 即 $C \supset S$；`CompressStrategy` 为策略 trait；Axiom SR1 由 trait 签名一致保证。

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Decorator](../02_structural/decorator.md) | 装饰器可持有多态策略 |
| [State](state.md) | 策略可替换；State 可转换 |
| [Template Method](template_method.md) | 同为算法定制；Strategy 为组合，Template 为继承等价 |

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| 泛型 `Context<S: Strategy>` | 编译期单态化，零成本 | 策略类型已知 |
| `Box<dyn Strategy>` | 运行时多态 | 策略动态选择 |
| `impl Strategy` 返回值 | 类型擦除，调用处不关心具体类型 | 作为函数返回值 |

---

## 反例：策略持有共享可变状态

**错误**：策略内部用 `static mut` 或 `Arc<Mutex<>>` 共享可变，多 Context 共享同一策略时产生隐式耦合。

```rust
struct BadStrategy { counter: Arc<Mutex<u32>> }
impl Strategy for BadStrategy {
    fn execute(&self, data: &[i32]) -> i32 {
        *self.counter.lock().unwrap() += 1;  // 隐式副作用
        data.iter().sum()
    }
}
```

**后果**：策略应有纯净输入输出；共享可变破坏可替换性（Axiom SR1）。

---

## 性能考虑

| 实现 | 开销 | 适用 |
| :--- | :--- | :--- |
| `Context<S: Strategy>` 泛型 | 零成本；单态化无虚调用 | 策略编译期确定 |
| `Context<Box<dyn Strategy>>` | 虚调用；一次间接 | 策略运行时选择 |
| `impl Strategy` 返回值 | 取决于具体类型；可能零成本 | API 隐藏实现 |

---

## 选型决策树

```text
需要可替换算法？
├── 是 → 编译期确定？ → Context<S: Strategy>（泛型）
│       └── 运行时选择？ → Box<dyn Strategy>
├── 需算法骨架+钩子？ → Template Method
└── 需状态转换？ → State
```

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |
