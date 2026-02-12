# Rust 惯用模式与设计理论衔接

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: 层次推进扩展

---

## 宗旨

将 Rust 社区惯用模式（Idioms）与软件设计理论、形式化基础衔接，提供**实质内容**：形式化对应、与 GoF 模式关系、典型场景、常见陷阱。

---

## 一、RAII（资源获取即初始化）

### 1.1 定义与形式化

**Def RAII1（RAII 惯用）**：资源生命周期与对象绑定；构造时获取、析构时释放；$\forall r \in \text{Resource},\, \exists x \in \text{Var}: \text{owns}(x, r) \land \text{scope\_end}(x) \rightarrow \text{release}(r)$。

**Axiom RAII1**：RAII 与 [ownership_model](../../formal_methods/ownership_model.md) 规则 3 一致；drop 顺序为创建逆序。

**定理 RAII-T1**：RAII 实现等价于 ownership 规则 3；`Drop::drop` 在 `scope_end` 时调用；由 [ownership_model](../../formal_methods/ownership_model.md) 定理 T3、BOX-T1。

### 1.2 典型场景

| 场景 | 实现 | 与 GoF 关系 |
| :--- | :--- | :--- |
| 文件句柄 | `File`、`BufReader` | 资源管理 |
| 锁 | `MutexGuard`、`RwLockReadGuard` | 与 Mutex 模式衔接 |
| 网络连接 | `TcpStream`、`impl Drop` | 资源管理 |
| 内存 | `Box`、`Vec` | 与 ownership 直接对应 |

### 1.3 常见陷阱

| 陷阱 | 后果 | 规避 |
| :--- | :--- | :--- |
| 循环引用 `Rc` | 内存泄漏 | 用 `Weak` 打破环 |
| 过早 drop | 悬垂引用 | 保证生命周期 outlives |
| 忘记 `impl Drop` | 资源泄漏 | 显式 RAII 封装 |

### 1.4 与设计模式衔接

- **Builder**：`build(self)` 消费后由调用方负责 drop；RAII 保证中间资源正确释放
- **Factory Method**：产品常为 RAII 类型；工厂返回 `Box<T>` 时 ownership 清晰
- **Proxy**：委托对象的 RAII 与 Proxy 一致；Proxy drop 时内部资源释放

---

## 二、Newtype 模式

### 2.1 定义与形式化

**Def NW1（Newtype）**：单字段包装类型，零成本抽象；`struct Newtype(T)`；`repr(transparent)` 保证布局与 `T` 一致。

**Axiom NW1**：Newtype 与底层类型布局相同；无运行时开销；类型层面区分语义。

**定理 NW-T1**：Newtype 满足 [ownership_model](../../formal_methods/ownership_model.md) 规则 1–3；`T` 的 ownership 语义直接传递；由 Def 1.3 无环、接口一致。

### 2.2 典型场景

| 场景 | 实现 | 与 GoF 关系 |
| :--- | :--- | :--- |
| 类型安全单位 | `struct Meter(f64)` | 类型区分 |
| 防止误用 | `struct UserId(u64)` | 与 DTO 衔接 |
| 品牌类型 | `struct Branded<T>` | 类型安全 |

### 2.3 常见陷阱

| 陷阱 | 后果 | 规避 |
| :--- | :--- | :--- |
| 忘记 `Deref` | 调用繁琐 | 按需 `impl Deref` |
| 过度包装 | 样板代码 | 仅在需语义区分时用 |
| 泄漏内部类型 | 封装破坏 | 谨慎 `pub` |

### 2.4 与设计模式衔接

- **Adapter**：Newtype 可作适配器包装；`impl Trait for Newtype` 委托
- **Value Object**：Fowler 的 Value Object 与 Newtype 等价；不可变、相等性
- **DTO**：Newtype 包装跨边界类型；与 02_complete_43_catalog DTO 衔接

---

## 三、类型状态模式（Typed State）

### 3.1 定义与形式化

**Def TS1（类型状态）**：类型参数编码状态；编译期强制合法转换；$\text{State}(F\langle S \rangle) \in \{S_1, \ldots, S_n\}$；仅允许的转换由类型系统约束。

**Axiom TS1**：非法状态转换导致编译错误；类型系统保证状态机正确性。

**定理 TS-T1**：类型状态与 [Builder](01_design_patterns_formal/01_creational/builder.md) B-T2 一致；类型状态 Builder 即 Def TS1 实例。

### 3.2 典型场景

| 场景 | 实现 | 与 GoF 关系 |
| :--- | :--- | :--- |
| Builder 必填 | `ConfigBuilder<SetHost>` → `ConfigBuilder<SetPort>` | Builder 变体 |
| 连接状态 | `Connection<Closed>` → `Connection<Open>` | State 变体 |
| 解析阶段 | `Parser<Initial>` → `Parser<Parsing>` | 流程控制 |

### 3.3 常见陷阱

| 陷阱 | 后果 | 规避 |
| :--- | :--- | :--- |
| 状态爆炸 | 类型过多 | 合并相近状态 |
| 泛型约束复杂 | 难以维护 | 文档化转换图 |
| 运行时分支 | 需 `dyn` | 优先编译期类型 |

### 3.4 与设计模式衔接

- **Builder**：类型状态 Builder 为 B-T2 的扩展；编译期强制顺序
- **State**：与 [state](01_design_patterns_formal/03_behavioral/state.md) 互补；编译期 vs 运行时状态机
- **Template Method**：trait 默认方法 + 类型状态可组合

---

## 四、Builder 变体（与 GoF 对照）

| 变体 | 说明 | 形式化文档 |
| :--- | :--- | :--- |
| Option + ok_or | 运行时校验 | [builder](01_design_patterns_formal/01_creational/builder.md) |
| 类型状态 Builder | 编译期强制 | [builder](01_design_patterns_formal/01_creational/builder.md) B-T2 |
| derive_builder | 宏生成 | 同上 |

---

## 五、与 23/43 模型衔接

| Idiom | 23 安全 | 43 完全 |
| :--- | :--- | :--- |
| RAII | 与所有权、Flyweight、Proxy 衔接 | 与 Unit of Work、Gateway 衔接 |
| Newtype | 与 Adapter、Value Object 衔接 | [02_complete_43_catalog](02_workflow_safe_complete_models/02_complete_43_catalog.md) Value Object |
| 类型状态 | 与 Builder、State 衔接 | 与 State 变体衔接 |

---

## 六、引用

- [rust-unofficial/patterns](https://rust-unofficial.github.io/patterns/)：Rust Idioms 官方来源
- [ownership_model](../../formal_methods/ownership_model.md)
- [01_design_patterns_formal](01_design_patterns_formal/README.md)
