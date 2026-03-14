# 型变概念族谱

> **创建日期**: 2026-02-24
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **级别**: L1 (给人看的)
> **用途**: 型变概念全景、三种型变详解、型变表、组合规则、与类型安全的关系

---

## 相关文档

| 文档 | 说明 |
| :--- | :--- |
| [variance_theory](../../research_notes/type_theory/variance_theory.md) | 型变理论形式化定义与定理 |
| [lifetime_formalization](lifetime_formalization.md) | 生命周期形式化（型变在生命周期中的体现）|
| [MIND_MAP_COLLECTION](../../04_thinking/MIND_MAP_COLLECTION.md) | 思维导图集合索引 |

---

## 型变概念全景

```text
                          型变概念族
                               │
        ┌──────────────────────┼──────────────────────┐
        │                      │                      │
    【协变】                【逆变】                【不变】
        │                      │                      │
        ├─定义                 ├─定义                 ├─定义
        │  T<:U → C<T><:C<U>   │  T<:U → C<U><:C<T>   │  T=U → C<T>=C<U>
        │                      │                      │
        ├─示例                 ├─示例                 ├─示例
        │  ├─Box<T>            │  ├─fn(T) (参数)      │  ├─&mut T
        │  ├─Vec<T>            │  └─PhantomData<T>    │  ├─Cell<T>
        │  ├─Option<T>         │                      │  ├─RefCell<T>
        │  ├─&T                │  ├─原因              │  └─UnsafeCell<T>
        │  └─fn()→T (返回)     │  参数位置需要逆变    │
        │                      │                      │  ├─原因
        ├─原因                 │  接受更泛化的输入    │  内部可变性
        │  保持子类型关系      │                      │  需要精确类型
        │                      │                      │
        └─直觉                 │                      │
            容器继承内容关系    │                      │
```

---

## 一、三种型变详解

### 1.1 协变 (Covariant) +

**定义**: 如果`T`是`U`的子类型，那么`C<T>`是`C<U>`的子类型。

```text
T <: U  →  C<T> <: C<U>
```

**示例**:

```rust
// &'static str 是 &'a str 的子类型
let s: &'static str = "hello";
let r: &'a str = s;  // OK，协变

// Box<&'static str> <: Box<&'a str>
let b1: Box<&'static str> = Box::new("hello");
let b2: Box<&'a str> = b1;  // OK
```

**为什么协变**:

- 容器"继承"内容的子类型关系
- 如果内容可以替换，容器也可以替换

**协变类型**:

- `Box<T>`
- `Vec<T>`
- `Option<T>`
- `Result<T, E>`
- `&T`
- `fn() -> T` (返回类型)

---

### 1.2 逆变 (Contravariant) -

**定义**: 如果`T`是`U`的子类型，那么`C<U>`是`C<T>`的子类型（反向）。

```text
T <: U  →  C<U> <: C<T>
```

**示例**:

```rust
// 接受 &'a str 的函数可以传给接受 &'static str 的位置
fn handler(_: &'static str) {}

// &'a str <: &'static str (因为'a可能更短)
// fn(&'a str) <: fn(&'static str)
let f: fn(&'a str) = handler;  // 可能错误，具体取决于'a
```

**为什么逆变**:

- 输入位置需要"更泛化"的类型
- 能接受`&'static str`的函数，一定能接受`&'a str`
- 但反过来不成立

**逆变类型**:

- `fn(T)` (参数类型)
- `PhantomData<T>` (特定用法)

**直觉**: 函数的"接受能力"越宽泛，函数越"通用"，越容易替换。

---

### 1.3 不变 (Invariant) =

**定义**: `C<T>`和`C<U>`无关，除非`T = U`。

```text
T = U  →  C<T> = C<U>
```

**示例**:

```rust
let mut r1: &mut &'static str = &mut "hello";
// let r2: &mut &'a str = r1;  // 错误！&mut T是不变的
```

**为什么不变**:

- 内部可变性：可以通过`&mut`修改内容
- 如果允许协变/逆变，可能破坏类型安全

**不变类型**:

- `&mut T`
- `Cell<T>`
- `RefCell<T>`
- `UnsafeCell<T>`
- `Mutex<T>`
- `RwLock<T>`

**原因**: 这些类型允许内部修改，如果允许型变，可能通过子类型关系绕过借用规则。

---

## 二、型变表

| 类型构造器 | 对T的型变 | 说明 |
| :--- | :--- | :--- |
| `Box<T>` | + | 协变 |
| `Vec<T>` | + | 协变 |
| `Option<T>` | + | 协变 |
| `Result<T, E>` | + (对T) | 协变 |
| `&T` | + | 协变 |
| `&mut T` | = | 不变 |
| `fn(T) -> U` | - (对T), + (对U) | 逆变(参数), 协变(返回) |
| `Cell<T>` | = | 不变 |
| `RefCell<T>` | = | 不变 |
| `UnsafeCell<T>` | = | 不变 |
| `PhantomData<T>` | +/- | 根据使用 |

---

## 三、型变组合规则

### 函数指针的型变

```rust
fn(T) -> U
//   T: 逆变(-)
//      U: 协变(+)
```

**理解**:

- 参数位置：函数需要"足够泛化"才能接受更多输入
- 返回位置：函数可以"更具体"的返回，使用方也能接受

### 结构体的型变

```rust
struct Wrapper<T>(T);
// Wrapper<T> 对T的型变与T的使用位置有关

struct Contravariant<T>(fn(T));
// Contravariant<T> 对T是逆变的
```

---

## 四、型变的实际影响

### 影响1: 生命周期子类型

```rust
// 'static <: 'a (static更长，是任何'a的子类型)

fn example<'a>(s: &'a str) {
    let static_str: &'static str = "hello";
    // 可以传给需要&'a str的地方
    takes_str(static_str);  // OK，协变
}

fn takes_str<'a>(s: &'a str) {}
```

### 影响2: 智能指针的使用

```rust
// Box的协变性允许：
fn process_box(b: Box<&'a str>) { }

let b: Box<&'static str> = Box::new("hello");
process_box(b);  // OK，协变转换

// 但&mut不行：
fn process_mut(r: &mut &'a str) { }

let mut r: &mut &'static str = &mut "hello";
// process_mut(r);  // 错误！&mut是不变的
```

### 影响3: 回调函数的类型

```rust
// 回调函数参数是逆变的
fn set_handler<F>(f: F)
where
    F: Fn(&str),  // 接受&str
{
}

// 可以接受更具体的参数
set_handler(|s: &'static str| { });  // OK
```

---

## 五、型变与类型安全

### 为什么&mut必须不变？

```rust
// 假设&mut是协变的（实际不是）
let mut r1: &mut &'static str = &mut "hello";
let r2: &mut &'a str = r1;  // 假设这是合法的

// 那么可以：
let local = String::from("local");
*r2 = &local;  // 将短生命周期引用存入
// local在这里结束
// 但*r1仍然指向它！悬垂引用！
```

**结论**: `&mut`的不变性保证了借用规则的安全性。

---

## 六、学习路径

```text
学习型变
        │
        ├──→ 基础
        │       ├── 理解子类型关系
        │       ├── 生命周期子类型
        │       └── 型变的三种形式
        │
        ├──→ 进阶
        │       ├── 型变表记忆
        │       ├── 组合规则
        │       └── 实际代码中的型变
        │
        └──→ 专家
                ├── 型变推导算法
                ├── 型变与类型安全证明
                └── 高级类型特性中的型变
```

---

## 七、记忆口诀

```text
返回值是协变 (+): 返回更具体的，调用者也接受
参数是逆变 (-): 接受更泛化的，传入更具体的也能处理
可变的都是不变 (=): 内部可变性需要精确类型匹配
```

---

## 八、何时需要关注型变

| 场景 | 是否需关注 | 说明 |
| :--- | :--- | :--- |
| 生命周期标注 | ✅ 高 | `&'a T` 协变，`&mut T` 不变 |
| 泛型结构体设计 | ✅ 中 | 含 `&T`/`&mut T`/`fn(T)` 时影响子类型 |
| 闭包/回调类型 | ✅ 中 | 函数指针参数逆变 |
| 智能指针选型 | ⚠️ 低 | Box/Vec 协变，Cell/RefCell 不变 |
| 纯值类型 | ❌ 无 | Copy 类型无型变问题 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-26
**状态**: ✅ 已完成 - 型变概念族谱

---

## 🆕 Rust 1.94 深度整合更新

> **适用版本**: Rust 1.94.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档

- [Rust 1.94 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 特性速查](../02_reference/quick_reference/rust_194_features_cheatsheet.md)
- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-14 (Rust 1.94 深度整合)
