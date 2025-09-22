# 设计与实现模式

> 返回索引：`docs/README.md`

本页汇总本仓库在模型/算法/形式化相关实现中反复使用的通用模式，并给出“何时使用/不要使用”、关键要点与简单片段，便于工程落地。

## 目录

- 不可变核心 + 受控可变状态（Interior Mutability 最小化）
- 构建器与校验分离（Builder + Validator）
- 零成本抽象与内联提示（Zero-cost Abstraction, #[inline])
- 错误分层（User/System/Assertion）
- 类型驱动配置（Strongly-typed Config）
- 有界资源与背压（Bounded Resource & Backpressure）
- 策略对象与泛型组合（Strategy via trait object/generics）
- 状态机 + 守卫（FSM + Guards）
- 数据管道（Preprocess → Train → Eval）
- 可观测性埋点（Tracing/Metrics）

---

## 不可变核心 + 受控可变状态

何时使用：核心模型结构体尽量不可变，训练/仿真中的少量状态通过受控 API 推进。

要点：

- 对外暴露不可变视图，内部必要时使用 `RefCell/Cell` 但限定边界。
- 将“推进”动作设计为显式方法，避免隐式共享可变引用。

```rust
pub struct ModelCore { params: Vec<f64> }
pub struct Runner { step: usize }

impl Runner {
    pub fn advance(&mut self, core: &ModelCore) { self.step += core.params.len(); }
}
```

## 构建器与校验分离

何时使用：初始化参数较多、需要一致性检查。

要点：

- `Builder` 只负责收集参数；`Validator`/`try_build` 进行集中校验并给出具体错误。

```rust
pub struct KMeansBuilder { pub k: usize, pub max_iter: usize }
impl KMeansBuilder { pub fn try_build(self) -> Result<KMeans, String> { if self.k==0 {return Err("k>0".into)}; Ok(KMeans::new(self.k, self.max_iter)) } }
```

## 零成本抽象与内联提示

要点：

- 对热路径标注 `#[inline]`，避免不必要的虚分发；必要时以泛型实现策略。

## 错误分层: 用户错误 / 系统错误 / 内部断言

要点：

- 对外返回可恢复错误（如维度不匹配）；系统级错误（I/O、数值不稳定）单独分类；内部不变量用断言保护并在测试覆盖。

```rust
pub enum ModelError { InvalidShape, Unstable, Io(std::io::Error) }
```

## 类型驱动配置

要点：

- 使用强类型承载超参数与单位（如率/时间），减少运行期错误。

## 有界资源与背压

场景：排队/并发模拟、数据流控。

要点：

- 明确容量上限与丢弃/阻塞策略；将背压作为一等公民配置。

## 策略对象与泛型组合

要点：

- 小规模策略数量固定时用枚举/泛型；运行时可插拔时用 trait 对象。

## 状态机 + 守卫

要点：

- 转换前置条件显式化；提供可达性/死锁检查工具。

## 数据管道（Preprocess → Train → Eval）

要点：

- 将预处理、训练、评估解耦；定义统一接口以便复用与测试。

## 可观测性埋点（Tracing/Metrics）

要点：

- 关键路径埋 `tracing` span；对外暴露基础指标（吞吐、延迟、收敛轮次）。

---

### 快速选型

- 配置多且需校验：优先 Builder + try_build
- 需要热路径策略：优先泛型；需运行时切换：trait 对象
- 高并发/容量敏感：有界资源 + 背压

### 最佳实践清单

- 明确不变式与断言；错误信息给出上下文
- 公共 API 保持不可变输入；返回结构自描述
- 给出小而可运行的示例与边界说明

---

## 交叉链接

- ML 管道与评估：`guides/ml-preprocess-eval.md`
- 状态机到协议验证：`guides/fsm-to-protocol.md`
- 排队与扩展性：`api-reference/queueing-models.md`
- 形式化模型 API：`api-reference/formal-models.md`

## 常见反模式

- 过度使用 `RefCell`/`Arc<Mutex<...>>`：优先不可变结构与最小可变边界
- 隐式共享可变：导致竞态与顺序依赖，改为显式推进 API
- 错误枚举过于宽泛：失去定位能力，建议分层并携带上下文
- 无界资源：缺少容量与背压策略，易触发级联退化
