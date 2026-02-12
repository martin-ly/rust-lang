# Rust 惯用模式与设计理论衔接

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 100% 完成

---

## 宗旨

将 Rust 社区惯用模式（Idioms）与软件设计理论、形式化基础衔接，提供**实质内容**：形式化对应、与 GoF 模式关系、典型场景、常见陷阱、代码示例。

---

## 层次推进（阅读顺序）

| 层次 | 内容 | 先修 |
| :--- | :--- | :--- |
| **L1 基础** | RAII、Newtype | 所有权、类型系统 |
| **L2 进阶** | 类型状态、Error handling | L1 |
| **L3 扩展** | Cow、Option/Result 模式、Builder 变体 | L2 |

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

### 1.3 完整代码示例

```rust
// RAII：文件句柄自动关闭
use std::fs::File;
use std::io::{BufRead, BufReader};

fn read_lines(path: &str) -> Result<Vec<String>, std::io::Error> {
    let f = File::open(path)?;           // 获取资源
    let buf = BufReader::new(f);
    buf.lines().collect()                 // 返回时 f、buf 自动 drop
}
// 若中间 panic，栈展开时按创建逆序 drop；无泄漏
```

```rust
// RAII：MutexGuard 自动释放锁
use std::sync::Mutex;

let m = Mutex::new(0);
{
    let mut g = m.lock().unwrap();       // 获取锁
    *g += 1;                              // 持锁期间修改
}                                         // 作用域结束，g drop，锁释放
```


### 1.4 常见陷阱

| 陷阱 | 后果 | 规避 |
| :--- | :--- | :--- |
| 循环引用 `Rc` | 内存泄漏 | 用 `Weak` 打破环 |
| 过早 drop | 悬垂引用 | 保证生命周期 outlives |
| 忘记 `impl Drop` | 资源泄漏 | 显式 RAII 封装 |

### 1.5 与设计模式衔接

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

### 2.3 完整代码示例

```rust
#[derive(Clone, PartialEq, Eq)]
pub struct UserId(pub u64);

#[derive(Clone, PartialEq, Eq)]
pub struct OrderId(pub u64);

fn process_order(user: UserId, order: OrderId) {
    // 类型系统防止：process_order(order_id, user_id) 错误
}
```

```rust
#[repr(transparent)]
pub struct Meter(f64);

impl Meter {
    pub fn new(v: f64) -> Self { Self(v) }
}
impl std::ops::Add for Meter {
    type Output = Meter;
    fn add(self, other: Meter) -> Meter { Meter(self.0 + other.0) }
}
// 零成本；防止 Meter + Kilogram 混用
```


### 2.4 常见陷阱

| 陷阱 | 后果 | 规避 |
| :--- | :--- | :--- |
| 忘记 `Deref` | 调用繁琐 | 按需 `impl Deref` |
| 过度包装 | 样板代码 | 仅在需语义区分时用 |
| 泄漏内部类型 | 封装破坏 | 谨慎 `pub` |

### 2.5 与设计模式衔接

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

---

---

## 六、Error handling 与 Result/? 惯用

### 6.1 定义与形式化

**Def EH1（Error handling 惯用）**：错误通过 `Result<T, E>` 显式传播；`?` 操作符实现早期返回；$\text{query}(e) \equiv \text{match } e \text{ with Ok}(v) \rightarrow v \mid \text{Err}(e) \rightarrow \text{return Err}(e.\text{into}())$。

**定理 EH-T1**：`?` 与 [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) Def QUERY1 一致；错误传播不违反借用规则。

### 6.2 典型场景

| 场景 | 实现 | 与设计模式关系 |
| :--- | :--- | :--- |
| 函数链错误传播 | `fn f() -> Result<T, E> { g()?; h()? }` | 与 Chain 模式衔接 |
| 错误转换 | `map_err`、`From` trait | Adapter 错误类型 |
| 可选操作 | `Option` + `ok_or` | 与 Builder 必填校验衔接 |

### 6.3 完整代码示例：错误传播链

```rust
#[derive(Debug)]
enum AppError {
    Io(std::io::Error),
    Parse(std::num::ParseIntError),
    Missing(String),
}

impl From<std::io::Error> for AppError {
    fn from(e: std::io::Error) -> Self { AppError::Io(e) }
}
impl From<std::num::ParseIntError> for AppError {
    fn from(e: std::num::ParseIntError) -> Self { AppError::Parse(e) }
}

fn read_config(path: &str) -> Result<u32, AppError> {
    let s = std::fs::read_to_string(path)?;           // Io → AppError
    let n: u32 = s.trim().parse().map_err(|e| AppError::Parse(e))?;
    Ok(n)
}

fn load_or_default(path: &str) -> Result<u32, AppError> {
    let s = std::fs::read_to_string(path)?;
    let n = s.trim().parse().unwrap_or(0);           // 解析失败时默认 0，避免 panic
    Ok(n)
}
```

### 6.4 常见陷阱

| 陷阱 | 后果 | 规避 |
| :--- | :--- | :--- |
| `unwrap()` 滥用 | panic 不可恢复 | 用 `?` 或 `match` 传播 |
| 错误类型不统一 | 传播繁琐 | `thiserror`、`From` 实现 |
| 忽略 `Result` | 静默失败 | 必须 `let _ =` 或显式处理 |

---

## 七、Option/Result 组合模式

### 7.1 定义与形式化

**Def OR1（Option/Result 组合）**：`Option` 表示可选值；`Result` 表示成功或错误；组合模式包括 `and_then`、`map`、`map_err`、`unwrap_or`、`ok_or`。

**定理 OR-T1**：`Option`/`Result` 与 [LANGUAGE_SEMANTICS_EXPRESSIVENESS](../../LANGUAGE_SEMANTICS_EXPRESSIVENESS.md) 构造性语义一致；无 null，无异常隐式传播。

### 7.2 典型场景

| 场景 | 实现 | 示例 |
| :--- | :--- | :--- |
| 链式可选 | `opt.and_then(\|x\| f(x))` | 解析链 |
| 默认值 | `opt.unwrap_or(default)` | 配置项 |
| 必填校验 | `opt.ok_or(Error::Missing)` | Builder 必填 |

### 7.3 完整代码示例：配置解析链

```rust
fn parse_port(env: &str) -> Option<u16> {
    std::env::var(env).ok()           // Option<String>
        .and_then(|s| s.parse().ok()) // Option<u16>
}

fn parse_config() -> Result<(String, u16), String> {
    let host = std::env::var("HOST").unwrap_or_else(|_| "localhost".into());
    let port = parse_port("PORT").ok_or("PORT must be set")?;
    Ok((host, port))
}

// 链式 Optional：仅当所有 Some 时继续
fn combine_all() -> Option<u32> {
    Some(1).and_then(|a| {
        Some(2).and_then(|b| {
            Some(3).map(|c| a + b + c)
        })
    })
}
```

### 7.4 与 Builder 必填校验衔接

```rust
struct ConfigBuilder {
    host: Option<String>,
    port: Option<u16>,
}
impl ConfigBuilder {
    fn build(self) -> Result<Config, String> {
        Ok(Config {
            host: self.host.ok_or("host required")?,
            port: self.port.ok_or("port required")?,
        })
    }
}
```

---

## 八、Cow（Clone-on-Write）模式

### 8.1 定义与形式化

**Def COW1（Cow）**：`Cow<'a, T>` 表示「借用或拥有」；可读时用 `&T` 避免复制；需写时克隆为 `T`。形式化：$\text{Cow} = \text{Borrowed}(\&T) \mid \text{Owned}(T)$；$\text{to\_mut}(c) \rightarrow \text{若 Borrowed 则 clone 转为 Owned}$。

**定理 COW-T1**：Cow 与 ownership 规则一致；读时不转移所有权；写时取得独占所有权。

### 8.2 典型场景

| 场景 | 实现 | 与设计模式关系 |
| :--- | :--- | :--- |
| 字符串处理 | `Cow<str>` | 避免不必要的 `String` 分配 |
| 配置解析 | 引用默认 +  owned 覆盖 | 与 Flyweight 共享思路衔接 |
| 条件克隆 | 仅修改时克隆 | 延迟复制 |

### 8.3 完整代码示例：字符串处理

```rust
use std::borrow::Cow;

fn process_string(s: &str) -> Cow<str> {
    if s.contains("bad") {
        Cow::Owned(s.replace("bad", "good"))
    } else {
        Cow::Borrowed(s)  // 无修改，直接借用
    }
}

fn prefix_if_needed(s: Cow<str>) -> Cow<str> {
    if s.starts_with("prefix:") {
        s
    } else {
        Cow::Owned(format!("prefix:{}", s))
    }
}

// 配置：默认值引用，覆盖时 owned
const DEFAULT: &str = "default";
fn get_config(override_val: Option<String>) -> Cow<str> {
    match override_val {
        Some(s) => Cow::Owned(s),
        None => Cow::Borrowed(DEFAULT),
    }
}
```

### 8.4 常见陷阱

| 陷阱 | 后果 | 规避 |
| :--- | :--- | :--- |
| 频繁 `to_mut()` | 丧失零成本 | 仅修改时调用 |
| 混用借用与 owned | 生命周期复杂 | 保证借用 outlives |

---

## 九、智能指针选型决策

| 需求 | 选型 | 形式化对应 |
| :--- | :--- | :--- |
| 独占堆 | `Box<T>` | [ownership_model](../../formal_methods/ownership_model.md) Def BOX1 |
| 单线程共享 | `Rc<T>` | Def RC1 |
| 跨线程共享 | `Arc<T>` | Def ARC1 |
| 内部可变单线程 | `RefCell<T>` | Def REFCELL1 |
| 可选写 | `Cow<'a, T>` | Def COW1 |
| 延迟初始化 | `OnceCell`/`LazyLock` | Singleton 模式 |

---

## 十、引用

- [rust-unofficial/patterns](https://rust-unofficial.github.io/patterns/)：Rust Idioms 官方来源
- [ownership_model](../../formal_methods/ownership_model.md)
- [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) Def QUERY1
- [01_design_patterns_formal](01_design_patterns_formal/README.md)
