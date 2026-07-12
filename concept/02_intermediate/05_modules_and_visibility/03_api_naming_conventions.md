# Rust API 命名约定

> **内容分级**: [中级]
>
> **代码状态**: ✅ 含可编译示例
>
> **EN**: Idiomatic Rust API Naming Conventions
> **Summary**: Rust API naming conventions aligned with the Rust API Guidelines and std library style.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [进阶]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: C×App — 将社区约定应用于实际 API 设计
> **定位**: 系统整理 Rust 标准库与生态中反复出现的命名模式，帮助学习者写出“看起来就像 Rust”的 API。
> **前置概念**: [Traits](../00_traits/01_traits.md) · [Generics](../01_generics/01_generics.md) · [Common Traits](../00_traits/01_traits.md)
> **后置概念**: [Design Patterns](../../06_ecosystem/03_design_patterns/01_patterns.md) · [Type System Patterns](../04_types_and_conversions/04_type_system_advanced.md)
> **来源**: [Google Comprehensive Rust — Predictable API](https://google.github.io/comprehensive-rust/idiomatic/foundations-api-design/predictable-api.html) · [Unicode UAX #31 — Identifier and Pattern Syntax](https://www.unicode.org/reports/tr31/) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [System F](https://en.wikipedia.org/wiki/System_F) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [Brown Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Rust Reference — Items](https://doc.rust-lang.org/reference/items.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/)
> [Rust API Guidelines — Naming](https://rust-lang.github.io/api-guidelines//naming.html) ·
> [RFC 430 / rust-lang/api-guidelines](https://rust-lang.github.io/api-guidelines/)
> **定理链**: N/A — 描述性/约定性文档，不涉及形式化定理链

---

## 📑 目录

- [Rust API 命名约定](#rust-api-命名约定)
  - [📑 目录](#-目录)
  - [一、为什么命名约定重要](#一为什么命名约定重要)
  - [二、构造函数](#二构造函数)
    - [2.1 `new`](#21-new)
    - [2.2 `with_`](#22-with_)
    - [2.3 `from_` / `into_`](#23-from_--into_)
    - [2.4 `try_`](#24-try_)
  - [三、谓词与查询](#三谓词与查询)
    - [3.1 `is_`](#31-is_)
    - [3.2 `as_` / `to_`](#32-as_--to_)
  - [四、可变访问](#四可变访问)
    - [4.1 `mut_`](#41-mut_)
  - [五、转换与构造](#五转换与构造)
    - [5.1 `to_`](#51-to_)
    - [5.2 `as_`](#52-as_)
    - [5.3 `into_`](#53-into_)
    - [5.4 `from`](#54-from)
  - [六、动作与回调](#六动作与回调)
    - [6.1 `by`](#61-by)
    - [6.2 `with` 闭包形式](#62-with-闭包形式)
  - [七、常见陷阱](#七常见陷阱)
  - [八、快速对照表](#八快速对照表)
  - [九、练习题](#九练习题)
    - [练习 1：为 `Config` 设计 API](#练习-1为-config-设计-api)
  - [相关概念](#相关概念)
  - [国际权威参考 / International Authority References（P1 学术 · P2 生态）](#国际权威参考--international-authority-referencesp1-学术--p2-生态)
  - [📋 关键属性](#-关键属性)
  - [🔗 概念关系](#-概念关系)

---

## 一、为什么命名约定重要

Rust 没有继承，也没有运算符重载的广泛自由。命名是 API 表达意图的主要方式 (Source: [Rust API Guidelines — Naming](https://rust-lang.github.io/api-guidelines/naming.html))。一致的命名能：

1. **降低认知负荷**：看到 `try_from` 就知道返回 `Result`。
2. **减少文档依赖**：`as_ref()` 与 `to_owned()` 的行为差异可通过前缀推断。
3. **与标准库对齐**：第三方 crate 若遵循相同约定，学习成本显著下降。

> **核心原则**：API 名字应回答“调用后会得到什么”以及“调用可能失败吗”。

---

## 二、构造函数

Rust 的构造约定（源自 [Rust API Guidelines: C-CTOR](https://rust-lang.github.io/api-guidelines/naming.html)）按「失败可能性 × 来源类型」区分四种命名：

- **`new`**：无参或全参的「主构造器」，假定不失败（如 `String::new`、`HashMap::new`）。一个类型至多一个 `new`；需要参数变体时用语义化名称（`with_capacity`）。`new` 不返回 `Result`——会失败的构造不叫 `new`。
- **`with_`**：以「某个关键配置」为参数的构造器（`Vec::with_capacity`、`TcpStream::with_timeout` 风格）——名称的 `_` 后接「构造的决定性差异」，读作「以 X 构造」。
- **`from_` / `into_`**：从其他类型转换而来。`from_` 用于「源类型不含在类型名中」的静态构造（`String::from_utf8`——失败版带 `_unchecked` 或返回 `Result`）；类型间转换优先实现 `From`/`Into` trait（`from` 无下划线版）而非自定义 `from_xxx`。
- **`try_`**：可能失败的转换/操作前缀（`str::try_from` 旧 API、`try_reserve`）——约定 `try_` 版本返回 `Result`/`Option`，无前缀版本要么不失败、要么 panic。成对出现时（`reserve`/`try_reserve`），调用方按「失败是否是正常路径」选择。

判定一个构造函数命名：失败可能 → `try_`；从单一源类型转换 → `from`/`from_`；以配置为区分 → `with_`；平凡构造 → `new`。

### 2.1 `new`

`new` 是类型主构造函数的默认名字，通常对应“最常用、无额外上下文的构造方式” (Source: [Rust API Guidelines — C-Ctor](https://rust-lang.github.io/api-guidelines/naming.html#c-ctor))。

```rust
pub struct Task {
    name: String,
    priority: u8,
}

impl Task {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            priority: 0,
        }
    }
}
```

> **约定**：一个类型通常只应有一个 `new`；若存在多种构造方式，用 `with_` / `from_` / `try_` 区分。

### 2.2 `with_`

当构造函数需要额外上下文或配置时使用 (Source: [Rust API Guidelines — C-Ctor](https://rust-lang.github.io/api-guidelines/naming.html#c-ctor))，常见形式：

- `with_capacity` — 预分配容量（`Vec::with_capacity`、`String::with_capacity`）
- `with_config` / `with_options` — 带配置对象
- `with_xxx` — 带某个特定属性

```rust,ignore
impl Task {
    pub fn with_priority(mut self, priority: u8) -> Self {
        self.priority = priority;
        self
    }
}

let task = Task::new("compile").with_priority(5);
```

> **认知提示**：`with_` 构造函数通常表示“在默认构造基础上追加配置”，返回同一类型。

### 2.3 `from_` / `into_`

用于从其他类型构造当前类型。若类型已实现 `From<T>`，通常不再重复提供 `from_xxx` 方法，除非需要额外参数 (Source: [Rust API Guidelines — C-From](https://rust-lang.github.io/api-guidelines/naming.html#c-from))。

```rust,ignore
impl Task {
    /// 从字符串切片构造，并自动分配默认 priority
    pub fn from_str(name: &str) -> Self {
        Self::new(name)
    }
}
```

> **优先顺序**：先实现标准 `From`/`TryFrom`；只有在需要额外参数时才使用 `from_xxx` 自由函数。

### 2.4 `try_`

当构造可能失败时，返回 `Result<Self, E>` (Source: [Rust API Guidelines — C-Try](https://rust-lang.github.io/api-guidelines/naming.html#c-try))。

```rust,ignore
#[derive(Debug)]
pub enum TaskError {
    EmptyName,
    PriorityTooHigh,
}

impl Task {
    pub fn try_new(name: impl Into<String>, priority: u8) -> Result<Self, TaskError> {
        let name = name.into();
        if name.is_empty() {
            return Err(TaskError::EmptyName);
        }
        if priority > 10 {
            return Err(TaskError::PriorityTooHigh);
        }
        Ok(Self { name, priority })
    }
}
```

> **约定**：`try_` 前缀暗示调用者必须处理错误，返回值类型通常为 `Result<T, E>`。

---

## 三、谓词与查询

谓词与查询方法的命名约定编码「返回什么 × 是否消耗/失败」：

- **`is_` / `has_` / `can_`**：返回 `bool` 的谓词，不失败、不消耗（`str::is_empty`、`Path::is_file`）。约定谓词方法取 `&self`、O(1) 或文档注明复杂度；`is_` 后接属性（`is_empty`），`has_` 后接持有物（`has_key` 风格），否定谓词优先用「`!x.is_empty()`」而非造 `is_not_empty`（`!is_empty` vs `len() > 0` 的 lint：clippy `len_zero` 要求容器提供 `is_empty`）。
- **`as_` / `to_` / `into_` 三件套**（C-CONV 约定）：按「借用-借用 / 借用-拥有 / 拥有-拥有」区分——`as_` 廉价借用视图（`str::as_bytes`，零拷贝，返回引用）；`to_` 昂贵的克隆式转换（`str::to_string`，分配）；`into_` 消耗 self 的转换（`String::into_bytes`，零拷贝转移缓冲区所有权）。三者的后缀类型名一致时，前缀即成本声明。

判定一个查询方法命名：返回引用且零成本 → `as_`；返回新拥有值且保留 self → `to_`；消耗 self → `into_`；返回 `bool` → `is_/has_`。违反约定的典型信号：名为 `as_` 却分配内存（成本名实不符），或名为 `to_` 却消耗 self（所有权名实不符）。

### 3.1 `is_`

返回 `bool` 的查询方法，不改变状态。

```rust,ignore
impl Task {
    pub fn is_high_priority(&self) -> bool {
        self.priority >= 7
    }
}
```

> **约定**：`is_xxx` 通常无副作用、不接收额外参数，且不应在内部修改状态。

### 3.2 `as_` / `to_`

用于返回某种视图或转换结果：

- `as_`：返回借用（Borrowing）/视图（cheap，通常不分配）
- `to_`：返回所有权（Ownership）转换结果（可能分配）

```rust,ignore
impl Task {
    /// 返回 name 的字符串切片视图
    pub fn as_name(&self) -> &str {
        &self.name
    }

    /// 将 Task 转换为“可显示”的字符串（分配新内存）
    pub fn to_summary(&self) -> String {
        format!("{} (priority {})", self.name, self.priority)
    }
}
```

---

## 四、可变访问

「可变访问」部分的核心主题是 `mut_`，本节展开说明。

### 4.1 `mut_`

返回可变引用（Mutable Reference）的访问器，对应 `xxx()` 的不可变版本。

```rust,ignore
impl Task {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn mut_name(&mut self) -> &mut String {
        &mut self.name
    }
}
```

> **注意**：现代 Rust 更推荐使用 `name_mut(&mut self)` 形式（动词后置），因为可读性更好：`task.name_mut().push_str("!");`。Google 课程两种形式都提及；标准库中既有 `get_mut` 也有 `iter_mut`，并无绝对统一。关键是：**同一 crate 内保持一致**。

---

## 五、转换与构造

转换四件套是 Rust API 命名中最精密的约定组（C-CONV），按「成本 × 所有权」二维定位：

| 前缀 | 输入 | 输出 | 成本承诺 | 典型示例 |
|:---|:---|:---|:---|:---|
| `as_` | `&self` | 引用/视图 | 免费（零拷贝） | `str::as_bytes`、`Path::as_os_str` |
| `to_` | `&self` | 拥有值 | 可能昂贵（克隆/分配） | `str::to_owned`、`Path::to_path_buf` |
| `into_` | `self` | 拥有值 | 通常免费（移动） | `String::into_bytes`、`Error::into_inner` |
| `from` | 关联函数 | `Self` | 不失败；失败版用 `try_from` | `String::from`、`u32::from_be_bytes` |

三条配套规则：① 类型间通用转换优先实现 `From`/`Into`/`TryFrom`/`TryInto` trait 而非造新名（`from`/`into` 无后缀版），方法版 `from_xxx` 保留给「源类型不止一个」的歧义场合；② `as_` 的输出类型名应与后缀一致（`as_mut`/`as_ref` 是特例）；③ 消耗 self 的转换必须 `into_` 开头——命名为 `to_` 却取 `self` by value 是违反 C-CONV 的 API 缺陷（clippy `wrong_self_convention` 捕获）。

判定一次转换设计的命名：先定所有权流向（借/克隆/移动），再按上表取前缀；失败可能性叠加 `try_`。

### 5.1 `to_`

`to_` 表示一个**可能分配、返回新所有权（Ownership）**的转换。

```rust
let s: String = "hello".to_string(); // 分配
let v: Vec<i32> = [1, 2, 3].to_vec(); // 分配
```

### 5.2 `as_`

`as_` 表示一个**廉价、返回借用（Borrowing）/视图**的转换。

```rust
let s = String::from("hello");
let slice: &str = s.as_str(); // 无分配
let bytes: &[u8] = s.as_bytes(); // 无分配
```

### 5.3 `into_`

`into_` 表示**消耗自身**的转换，常与 `From`/`Into` trait 配合使用。

```rust,ignore
impl Task {
    /// 消耗 Task，返回其 name 的所有权
    pub fn into_name(self) -> String {
        self.name
    }
}

let name: String = "hello".into(); // String: From<&str>
let task = Task::new("hello");
let owned_name: String = task.into_name(); // 消耗 Task
```

### 5.4 `from`

标准 trait `From<T>` 的实现方法。若一个类型可从多种源构造，优先实现 `From` 而非手写多个 `from_xxx`。

```rust,ignore
impl From<&str> for Task {
    fn from(name: &str) -> Self {
        Self::new(name)
    }
}
```

---

## 六、动作与回调

本节围绕「动作与回调」展开，覆盖 `by` 与  `with` 闭包形式 两个方面。

### 6.1 `by`

`by` 表示“通过某种方式执行动作”，常见于排序、比较、分组等 API。

```rust,ignore
// 标准库风格
items.sort_by(|a, b| a.priority.cmp(&b.priority));
items.sort_by_key(|item| item.priority);

// 自定义示例：对 Vec<Task> 按优先级排序
fn prioritize_by<F>(tasks: &mut Vec<Task>, mut f: F)
where
    F: FnMut(&Task, &Task) -> std::cmp::Ordering,
{
    tasks.sort_by(f);
}
```

### 6.2 `with` 闭包形式

接收闭包（Closures）以自定义行为的 API，通常用 `with_` 前缀。

```rust,ignore
fn with_each_task<F>(tasks: &[Task], mut f: F)
where
    F: FnMut(&Task),
{
    for task in tasks {
        f(task);
    }
}
```

---

## 七、常见陷阱

| 反模式 | 问题 | 推荐 |
|:---|:---|:---|
| `get_x()` 返回 `&T` 的同时还有 `x()` | 命名冗余，易混淆 | 只保留 `x()` 和 `x_mut()` |
| `convert_to_string()` | 未利用 `to_` / `into_` 约定 | 使用 `to_string()` 或 `into_string()` |
| `make_new()` | 与 `new()` 语义重复 | 直接使用 `new()` |
| `try_do()` 返回 `Option<T>` | 前缀与返回类型不匹配 | 返回 `Result` 用 `try_`，返回 `Option` 用 `maybe_` 或不加 |
| `is_xxx(&mut self)` | 谓词方法修改状态 | 改为 `take_xxx()` / `consume_xxx()` 或拆分 |

---

## 八、快速对照表

| 前缀/后缀 | 含义 | 返回类型 | 示例 |
|:---|:---|:---:|:---|
| `new` | 主构造函数 | `Self` | `Vec::new()` |
| `with_` | 带额外配置的构造函数 | `Self` | `Vec::with_capacity(10)` |
| `try_` | 可能失败的构造函数/动作 | `Result<T, E>` | `Task::try_new(...)` |
| `is_` | 状态查询 | `bool` | `is_empty()` |
| `as_` | 廉价视图/借用（Borrowing） | `&U` / `&mut U` | `as_str()` |
| `to_` | 分配式转换 | `U`（_owned_） | `to_string()` |
| `into_` | 消耗式转换 | `U`（_owned_） | `into_inner()` |
| `from` | 标准 `From` trait | `Self` | `String::from("x")` |
| `mut_` / `_mut` | 可变引用（Mutable Reference）访问器 | `&mut U` | `get_mut()` |
| `by` / `by_key` | 通过闭包（Closures）/key 执行 | varies | `sort_by()` |

---

## 九、练习题

「练习题」部分的核心主题是练习 1：为 `Config` 设计 API，本节展开说明。

### 练习 1：为 `Config` 设计 API

给定以下结构，为其选择合理的命名：

```rust
pub struct Config {
    host: String,
    port: u16,
}
```

应提供：

- 主构造函数
- 从 `(&str, u16)` 构造的 `From` 实现
- 返回 host 不可变/可变引用（Mutable Reference）的访问器
- 判断端口是否为默认 HTTP 端口（80）的谓词
- 将配置序列化为 `String` 的方法（分配新内存）

<details>
<summary>参考答案</summary>

```rust
pub struct Config {
    host: String,
    port: u16,
}

impl Config {
    pub fn new(host: impl Into<String>, port: u16) -> Self {
        Self {
            host: host.into(),
            port,
        }
    }

    pub fn host(&self) -> &str {
        &self.host
    }

    pub fn host_mut(&mut self) -> &mut String {
        &mut self.host
    }

    pub fn is_default_http_port(&self) -> bool {
        self.port == 80
    }

    pub fn to_uri(&self) -> String {
        format!("{}:{}", self.host, self.port)
    }
}

impl From<(&str, u16)> for Config {
    fn from((host, port): (&str, u16)) -> Self {
        Self::new(host, port)
    }
}
```

</details>

---

## 相关概念

- [Functions](../../01_foundation/07_modules_and_items/02_functions.md) — 函数命名与签名设计的基础语法
- [Items](../../01_foundation/07_modules_and_items/12_items.md) — 可被命名的各类语言项（item）总览

---

> **过渡**: 掌握命名约定后，可进一步学习 [Type System Patterns](../04_types_and_conversions/04_type_system_advanced.md) 中的 Newtype、Typestate、RAII 等模式，将命名与类型设计结合起来。

---

> **权威来源**: [Rust API Guidelines — Naming](https://rust-lang.github.io/api-guidelines/naming.html), [TRPL](https://doc.rust-lang.org/book/title-page.html), [Rust Reference — Items](https://doc.rust-lang.org/reference/items.html), [Unicode UAX #31](https://www.unicode.org/reports/tr31/)
> **权威来源对齐变更日志**: 2026-07-10 对齐权威来源
> **状态**: ✅ 权威来源对齐完成

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/toml — 生态权威 API 文档](https://docs.rs/toml) · [docs.rs/cargo_metadata — 生态权威 API 文档](https://docs.rs/cargo_metadata)

## 📋 关键属性

| 属性 | 取值 / 判定 | 依据 |
|---|---|---|
| 构造 | `new` 惯例；转换用 `from_` / `into_` 前缀 | API Guidelines |
| 谓词 | `is_` / `has_` 前缀返回 `bool` | 命名惯例 |
| 可变访问 | getter 无后缀，setter 用 `set_` 或 `mut_` | 命名惯例 |
| 转换语义 | `as_`（借用）/ `to_`（克隆）/ `into_`（消耗）成本递增 | 命名语义 |
| 一致性 | 遵循 std 先例降低认知负荷 | 设计哲学 |

## 🔗 概念关系

- **上位（is-a）**：[Module System](01_module_system.md) 公共接口设计的语义层。
- **下位（实例）**：各命名类别实例见本页「快速对照表」。
- **对偶**：与自由命名（无约定）相对——约定即文档。
- **组合**：与 [Traits](../00_traits/01_traits.md) 的 `From`/`Into` 契约组合。
- **依赖**：转换语义对应 [Error Handling Basics](../../01_foundation/08_error_handling/01_error_handling_basics.md) 的 `TryFrom` 约定。
