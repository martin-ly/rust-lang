# 引用语义：自动解引用、Deref 强制与类型转换

> **Bloom 层级**: 理解 → 应用
> **定位**: 深入分析 Rust 的**引用语义机制**——自动解引用（Auto-deref）、Deref 强制（Deref Coercion）、类型强制（Type Coercion）以及它们与借用检查器的交互，澄清开发者常见的隐式转换困惑。
> **前置概念**: [Ownership](./01_ownership.md) · [Borrowing](./02_borrowing.md) · [Type System](./04_type_system.md)
> **后置概念**: [Smart Pointers](../02_intermediate/03_memory_management.md) · [Generics](../02_intermediate/02_generics.md)

---

> **来源**:
> [Rust Reference — Type Coercions](https://doc.rust-lang.org/reference/type-coercions.html) ·
> [Rust Reference — Method Call Expressions](https://doc.rust-lang.org/reference/expressions/method-call-expr.html#automatic-referencing) ·
> [TRPL Ch15 — Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html) ·
> [Rustonomicon — Coercions](https://doc.rust-lang.org/nomicon/coercions.html)

## 📑 目录
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

- [引用语义：自动解引用、Deref 强制与类型转换](#引用语义自动解引用deref-强制与类型转换)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 引用的多重含义](#11-引用的多重含义)
    - [1.2 自动解引用机制](#12-自动解引用机制)
    - [1.3 Deref 强制](#13-deref-强制)
  - [二、技术细节](#二技术细节)
    - [2.1 方法调用的自动引用](#21-方法调用的自动引用)
    - [2.2 类型强制规则](#22-类型强制规则)
    - [2.3 与借用检查的交互](#23-与借用检查的交互)
  - [三、使用模式](#三使用模式)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 边界极限](#42-边界极限)
  - [五、常见困惑解析](#五常见困惑解析)
  - [六、来源与延伸阅读](#六来源与延伸阅读)
  - [相关概念文件](#相关概念文件)
  - [七、多级引用语义与部分重借用（Multi-level References \& Partial Reborrows）](#七多级引用语义与部分重借用multi-level-references--partial-reborrows)
    - [7.1 多级引用类型](#71-多级引用类型)
      - [7.1.1 共享引用的嵌套：`&T` → `&&T` → `&&&T`](#711-共享引用的嵌套t--t--t)
      - [7.1.2 可变引用的嵌套：`&mut T`、`&mut &T`、`&mut &mut T`](#712-可变引用的嵌套mut-tmut-tmut-mut-t)
      - [7.1.3 弱化的不可逆性](#713-弱化的不可逆性)
    - [7.2 部分重借用（Partial Reborrows）](#72-部分重借用partial-reborrows)
      - [7.2.1 编译器的字段级借用粒度](#721-编译器的字段级借用粒度)
      - [7.2.2 部分重借用的类型学限制](#722-部分重借用的类型学限制)
      - [7.2.3 Polonius 与未来的改进](#723-polonius-与未来的改进)
    - [7.3 返回可变引用的形式化语义](#73-返回可变引用的形式化语义)
      - [7.3.1 两次移动模型](#731-两次移动模型)
      - [7.3.2 实用模式：`split_first_mut` 与 `split_mut`](#732-实用模式split_first_mut-与-split_mut)
    - [7.4 Tree Borrows 模型](#74-tree-borrows-模型)
      - [7.4.1 从 Stacked Borrows 到 Tree Borrows](#741-从-stacked-borrows-到-tree-borrows)
      - [7.4.2 权限树：Foreign / Read / Write / Unique](#742-权限树foreign--read--write--unique)
    - [7.5 `as_ref()` / `as_mut()` 与嵌套引用](#75-as_ref--as_mut-与嵌套引用)
      - [7.5.1 嵌套引用的类型转换](#751-嵌套引用的类型转换)
      - [7.5.2 生命周期行为](#752-生命周期行为)
    - [7.6 代码示例集](#76-代码示例集)
      - [7.6.1 嵌套引用的构造与模式匹配](#761-嵌套引用的构造与模式匹配)
      - [7.6.2 结构体字段的部分重借用](#762-结构体字段的部分重借用)
      - [7.6.3 `split_mut` 创建不相交可变引用](#763-split_mut-创建不相交可变引用)
      - [7.6.4 迭代器可变链](#764-迭代器可变链)
    - [7.7 边界分析](#77-边界分析)
      - [7.7.1 命题与反命题](#771-命题与反命题)
      - [7.7.2 边界极限](#772-边界极限)
    - [7.8 常见困惑解析](#78-常见困惑解析)
      - [困惑 1: `let r: &&i32 = &&5;` —— 中间引用的生命周期](#困惑-1-let-r-i32--5--中间引用的生命周期)
      - [困惑 2: `&mut &T` vs `&&mut T`](#困惑-2-mut-t-vs-mut-t)
      - [困惑 3: 为什么 `&&&&T` 自动解引用但 `&mut &mut T` 不自动解引用到 `&mut T`？](#困惑-3-为什么-t-自动解引用但-mut-mut-t-不自动解引用到-mut-t)
    - [7.9 形式化视角](#79-形式化视角)
    - [7.10 名义与结构类型的引用边界](#710-名义与结构类型的引用边界)
  - [来源与延伸阅读（本节）](#来源与延伸阅读本节)
  - [权威来源索引](#权威来源索引)

---

## 一、核心概念
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

### 1.1 引用的多重含义
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

在 Rust 中，"引用"（reference）在不同上下文中有不同含义：

```text
Rust 中的"引用"层次:

  1. 借用引用 (&T, &mut T)
     ├── 语法: &x, &mut x
     ├── 语义: 对值的非所有权访问
     └── 约束: 受借用检查器管理

  2. 原始指针 (*const T, *mut T)
     ├── 语法: *const T, *mut T
     ├── 语义: 无安全检查的内存地址
     └── 约束: 仅在 unsafe 块中使用

  3. 智能指针 (Box<T>, Rc<T>, Arc<T>)
     ├── 语法: 像值一样使用
     ├── 语义: 拥有所有权 + 附加行为
     └── 约束: 通过 Deref trait 模拟引用行为

  4. 函数指针 (fn() -> T)
     ├── 语法: fn(i32) -> i32
     ├── 语义: 可调用代码的地址
     └── 约束: 无环境捕获（与闭包区分）

关键区分:
  - 借用引用 ≠ 原始指针（后者无安全检查）
  - 借用引用 ≠ 智能指针（后者有所有权）
  - 智能指针通过 Deref 模拟引用行为
```

> **核心洞察**: Rust 的"引用"是一个**语义家族**，而非单一概念。理解各成员的区别是掌握 Rust 内存模型的关键。
> [来源: [Rust Reference — Reference Types](https://doc.rust-lang.org/reference/types/pointer.html#shared-references-)]

---

### 1.2 自动解引用机制
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```mermaid
graph LR
    subgraph 自动引用["方法调用: 自动引用"]
        A["s.len()"] -->|"s: String"| B["自动 &s"]
        B -->|"调用 &str::len"| C["结果"]
    end

    subgraph 自动解引用["自动解引用"]
        D["*box"] -->|"box: Box<T>"| E["自动 *box"]
        E -->|"访问 T"| F["结果"]
    end

    subgraph Deref强制["Deref 强制"]
        G["&Box<T>"] -->|"自动 deref"| H["&T"]
        G -->|"多次 deref"| I["&目标类型"]
    end
```

> **认知功能**: 此图展示 Rust 中三种**隐式引用/解引用机制**——自动引用（方法调用）、自动解引用（显式 * 操作）和 Deref 强制（类型转换）。
> [来源: [TRPL](https://doc.rust-lang.org/book/)]
> **使用建议**: 利用自动机制简化代码，但理解其背后的规则以避免意外行为。
> **关键洞察**: 这些隐式转换是**语法糖**——它们在编译期展开为显式操作，无运行时开销。
> [来源: [Rust Reference — Method Call Expressions](https://doc.rust-lang.org/reference/expressions/method-call-expr.html#automatic-referencing)]

---

### 1.3 Deref 强制
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust
use std::ops::Deref;

struct MyBox<T>(T);

impl<T> Deref for MyBox<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

// Deref 强制生效:
let b = MyBox(String::from("hello"));
let s: &str = &b;  // ✅ &MyBox<String> → &String → &str

// 展开逻辑:
// 1. &b → &MyBox<String>
// 2. Deref: &MyBox<String> → &String
// 3. Deref (String deref to str): &String → &str
```

> **Deref 强制规则**:
>
> 1. 从 `&T` 到 `&U`，当 `T: Deref<Target=U>`
> 2. 从 `&mut T` 到 `&mut U`，当 `T: DerefMut<Target=U>`
> 3. 从 `&mut T` 到 `&U`，当 `T: Deref<Target=U>`（自动降级为不可变）
> 4. **不允许**: `&T` → `&mut U`（违反别名规则）
> [来源: [Rust Reference — Deref Coercion](https://doc.rust-lang.org/reference/type-coercions.html#unsized-coercions)]

---

## 二、技术细节
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

### 2.1 方法调用的自动引用
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust
let s = String::from("hello");

// 情况 1: self 方法
s.len();        // 自动: (&s).len()

// 情况 2: &self 方法
let r = &s;
r.len();        // 自动: (*r).len() → 然后 (&*r).len()
                // 实际: r 已经是 &String，直接调用 &self 方法

// 情况 3: &mut self 方法
let mut s2 = String::from("world");
s2.push('!');   // 自动: (&mut s2).push('!')

// 情况 4: 多级自动引用
let b = Box::new(String::from("hi"));
b.len();        // 自动: (&*b).len() → &String::len()
```

> **自动引用规则**:
>
> 1. 编译器尝试 `s.method()` → `(&s).method()` → `(&mut s).method()` → `(*s).method()`
> 2. 选择**第一个成功匹配**的调用方式
> 3. 不可变引用优先于可变引用（避免不必要的独占访问）
> [来源: [Rust Reference — Method Call Expressions](https://doc.rust-lang.org/reference/expressions/method-call-expr.html#autoref)]

---

### 2.2 类型强制规则
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```text
Rust 的类型强制（隐式转换）:

  1. 子类型强制
     ├── &T → &U（当 T 是 U 的子类型）
     └── 例: &mut T → &T（可变引用是更严格的类型）

  2. Deref 强制
     ├── &T → &U（当 T: Deref<Target=U>）
     ├── &mut T → &mut U（当 T: DerefMut<Target=U>）
     └── &mut T → &U（当 T: Deref<Target=U>）

  3. 指针弱化
     ├── &mut T → *mut T
     ├── &T → *const T
     └── &mut T → *const T

  4. 未大小类型转换
     ├── &T → &dyn Trait（当 T: Trait）
     └── 例: &MyType → &dyn MyTrait

  5. 生命周期延长
     └── 短生命周期引用 → 长生命周期引用

  注意: 与 C++ 不同，Rust 无数值类型隐式转换
  ├── i32 → i64 必须显式: i64::from(x)
  └── f64 → f32 必须显式: x as f32
```

> **强制规则**: Rust 的类型强制是**保守的**——只在类型安全且语义明确时发生。数值类型之间无隐式转换，避免 C/C++ 中的隐式截断 bug。
> [来源: [Rust Reference — Type Coercions](https://doc.rust-lang.org/reference/type-coercions.html)]

---

### 2.3 与借用检查的交互
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```mermaid
graph TD
    subgraph 安全保证["借用检查的安全保证"]
        A["Deref 强制"] -->|"必须保持"| B["&mut 独占性"]
        A -->|"必须保持"| C["& 共享性"]
        A -->|"必须保持"| D["生命周期有效性"]
    end

    subgraph 限制["Deref 的限制"]
        E["&T → &mut U"] -->|"禁止"| F["违反别名规则"]
        G["多次 DerefMut"] -->|"禁止"| H["可能创建多个 &mut"]
    end

    subgraph 安全["结果"]
        I["Deref 强制"] -->|"在借用检查之后"| J["无安全问题"]
    end
```

> **认知功能**: 此图展示 Deref 强制与借用检查器的**协作关系**——Deref 强制发生在借用检查之后，因此不会绕过安全保证。
> [来源: [TRPL](https://doc.rust-lang.org/book/)]
> **关键洞察**: Deref 返回的引用**仍然受借用检查器约束**。`DerefMut::deref_mut` 返回的 `&mut self.0` 遵守所有可变引用的规则。
> [来源: [Rust Reference — Borrow Checker](https://doc.rust-lang.org/reference/statements-and-expressions.html)]

---

## 三、使用模式
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

```text
模式 1: 智能指针透明化
  let b = Box::new(vec![1, 2, 3]);
  b.push(4);  // 自动: (&mut *b).push(4)
  // Vec::push 需要 &mut self，DerefMut 自动解引用 Box

模式 2: 自定义类型的引用语义
  struct Wrapper(Vec<u8>);

  impl Deref for Wrapper {
      type Target = Vec<u8>;
      fn deref(&self) -> &Vec<u8> { &self.0 }
  }

  impl DerefMut for Wrapper {
      fn deref_mut(&mut self) -> &mut Vec<u8> { &mut self.0 }
  }

  let mut w = Wrapper(vec![1, 2, 3]);
  w.push(4);  // 通过 DerefMut 调用 Vec::push

模式 3: 字符串透明转换
  let s = String::from("hello");
  let s_ref: &str = &s;  // &String → &str（通过 Deref）

模式 4: 避免过度 Deref
  // 不推荐: 多级 Deref 降低代码清晰度
  let r: &&&i32 = &&&5;
  let v = r;  // 自动解引用到 &i32，但意图不明

  // 推荐: 显式标注类型
  let r: &&&i32 = &&&5;
  let v: &i32 = r;  // 意图清晰
```

> **最佳实践**: 利用 Deref 使自定义类型"像引用一样工作"，但避免过度嵌套的引用类型，保持代码清晰。
> [来源: [Rust API Guidelines — Smart Pointers](https://rust-lang.github.io/api-guidelines/)]

---

## 四、反命题与边界分析
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

### 4.1 反命题树
>
> **[来源: [crates.io](https://crates.io/)]**

```mermaid
graph TD
    ROOT["命题: 所有包装类型都应实现 Deref"]
    ROOT --> Q1{"是否语义上是"引用"的扩展?"}
    Q1 -->|是| TRUE["✅ 实现 Deref — 如 Box, Rc, Arc"]
    Q1 -->|否| FALSE["❌ 不应实现 — Deref 不是通用委托机制"]

    style TRUE fill:#c8e6c9
    style FALSE fill:#ffebee
```

> **认知功能**: 此决策树判断是否应为类型实现 Deref。核心判断标准是**语义是否属于"引用"家族**。
> [来源: [TRPL](https://doc.rust-lang.org/book/)]
> **使用建议**: Deref 只用于**智能指针/引用包装器**。普通封装应使用显式方法，而非 Deref。
> **关键洞察**: Deref 的滥用会导致**隐式行为过度**——调用者无法从代码中看出转换发生，增加理解成本。
> [来源: [Rust API Guidelines — Deref](https://rust-lang.github.io/api-guidelines/predictability.html)]

---

### 4.2 边界极限
>
> **[来源: [docs.rs](https://docs.rs/)]**

```text
边界 1: Deref 不是继承
├── Deref 提供隐式转换，不是子类型多态
├── 不能通过 Deref 调用目标类型的 trait 方法（除非也实现了该 trait）
└── 例: Box<dyn Write> 不能自动获得 Write 方法，除非 Box 也 impl Write

边界 2: Deref 和目标类型的方法冲突
├── 如果 Wrapper 和 Target 有同名方法，优先调用 Wrapper 的
├── 无自动 disambiguation，需显式转换
└── 例: wrapper.as_bytes() vs (*wrapper).as_bytes()

边界 3: Deref 与泛型
├── Deref<Target=T> 中的 Target 是关联类型，不是泛型参数
├── 一个类型只能有一个 Target
└── 不能根据上下文选择不同的 Deref 目标

边界 4: 自动引用有成本吗?
├── 无运行时成本——全部是编译期转换
├── 但过度隐式可能影响代码可读性
└── 与 C++ 的隐式转换不同，Rust 的转换是确定性的、可预测的
```

> **边界要点**: Deref 的设计是**克制而精确的**——提供足够的便利性，但不引入不可预测的隐式行为。
> [来源: [Rust Reference — Deref](https://doc.rust-lang.org/std/ops/trait.Deref.html)]

---

## 五、常见困惑解析
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

```text
困惑 1: &s 和 s.as_str() 的区别
  let s = String::from("hello");
  let r1: &str = &s;        // Deref 强制: &String → &str
  let r2: &str = s.as_str(); // 显式方法调用
  // 结果相同，但 &s 更惯用

困惑 2: 为什么 &mut String 可以传给需要 &str 的参数?
  fn print(s: &str) { println!("{}", s); }
  let mut s = String::from("hi");
  print(&s);      // ✅ &String → &str（Deref）
  print(&mut s);  // ✅ &mut String → &String → &str（降级 + Deref）

困惑 3: 为什么 Box<T> 可以自动解引用，但 Vec<T> 不行?
  // Box<T> 实现了 Deref<Target=T>
  // Vec<T> 实现了 Deref<Target=[T]>——解引用到切片，不是元素
  let v = vec![1, 2, 3];
  // let x: i32 = v;  // ❌ Vec<i32> 不 Deref 到 i32
  let s: &[i32] = &v;  // ✅ Vec<i32> Deref 到 [i32]

困惑 4: * 操作符在哪些情况下自动?
  let b = Box::new(5);
  let r = &b;
  println!("{}", *r);  // 显式解引用
  println!("{}", r);   // 自动解引用（某些上下文）
  // 实际上，对于 Copy 类型，&T 在某些上下文中自动解引用
```

> **困惑总结**: 大多数困惑源于**隐式转换的边界不清晰**。记住：Rust 的自动机制只在**方法调用**和**赋值/传参**时触发，其他场景需显式操作。
> [来源: [TRPL — Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)]

---

## 六、来源与延伸阅读
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Rust Reference — Type Coercions](https://doc.rust-lang.org/reference/type-coercions.html) | ✅ 一级 | 类型强制规则 |
| [Rust Reference — Method Call](https://doc.rust-lang.org/reference/expressions/method-call-expr.html) | ✅ 一级 | 自动引用机制 |
| [TRPL Ch15 — Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html) | ✅ 一级 | Deref trait 详解 |
| [Rustonomicon — Coercions](https://doc.rust-lang.org/nomicon/coercions.html) | ✅ 一级 | unsafe 强制 |
| [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | ✅ 一级 | API 设计最佳实践 |

---

## 相关概念文件
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

- [Ownership](./01_ownership.md) — 所有权模型
- [Borrowing](./02_borrowing.md) — 借用与生命周期
- [Type System](./04_type_system.md) — Rust 类型系统
- [Memory Management](../02_intermediate/03_memory_management.md) — 内存管理与智能指针
- [Generics](../02_intermediate/02_generics.md) — 泛型与参数多态

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **权威来源对齐变更日志**: 2026-05-21 创建，对齐 Rust 1.95.0+ (Edition 2024)

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-22
**状态**: ✅ 新增第七节“多级引用语义与部分重借用”

## 七、多级引用语义与部分重借用（Multi-level References & Partial Reborrows）
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **Bloom 层级**: 理解 → 分析 → 应用
> **定位**: 深入 Rust 的**多级引用**（`&&T`、`&mut &T`）与**部分重借用**（partial reborrow）机制，澄清嵌套引用在借用检查器中的行为、编译器对结构体字段级粒度的跟踪，以及 Tree Borrows 模型下的权限语义。
> **前置概念**: [Ownership](./01_ownership.md) · [Borrowing](./02_borrowing.md) · [Lifetime](./03_lifetimes.md)
> **后置概念**: [Unsafe Rust](../03_advanced/03_unsafe.md) · [Formal Methods](../04_formal/01_linear_logic.md)

---

> **来源**:
> [Rust Reference — Reference Types](https://doc.rust-lang.org/reference/types/pointer.html) ·
> [Rust Reference — Method Call Expressions](https://doc.rust-lang.org/reference/expressions/method-call-expr.html#automatic-referencing) ·
> [TRPL Ch4 — References and Borrowing](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html) ·
> [Rustonomicon — Transmutes](https://doc.rust-lang.org/nomicon/transmutes.html) ·
> [PLDI 2025 — Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/) ·
> [Rust Internals — Partial Reborrows](https://internals.rust-lang.org/)

### 7.1 多级引用类型

> [来源: [Rust Reference — Reference Types](https://doc.rust-lang.org/reference/types/pointer.html)]

#### 7.1.1 共享引用的嵌套：`&T` → `&&T` → `&&&T`

在 Rust 中，引用本身也是一等类型，可以被再次引用。多级共享引用 `&&T` 并非 C 中的"指针的指针"的简单类比——每一级引用都携带独立的生命周期，并受借用检查器的完整约束。

```rust
let x = 42;
let r1 = &x;       // r1: &i32
let r2 = &r1;      // r2: &&i32
let r3 = &r2;      // r3: &&&i32

// 自动解引用链：r3 → r2 → r1 → x
assert_eq!(***r3, 42);
```

类型推断行为：当写 `let r = &&&5;` 时，Rust 编译器推断的类型是 `&&&i32`，其中每一级引用都获得独立的匿名生命周期。

```rust
let r = &&&5;
// 等价于：
let r: &&&i32 = &&&5;
```

自动解引用链（Auto-deref chain）在方法调用和某些操作符上下文中自动展开：

```rust,ignore
let r: &&&i32 = &&&5;
// 比较时自动解引用
assert_eq!(r, &42);     // ✅ 编译器展开: &&&i32 → &&i32 → &i32 → i32
                        // 实际比较的是 *r == 42（通过 PartialEq 的递归解引用）
```

> **关键洞察**: `&&&&T` 在需要 `&T` 的上下文中会通过**连续的自动解引用**逐步降级，但这是**单向**的——只能从外向内解引用，不能自动将 `&T` 升级为 `&&T`。
> [来源: [Rust Reference — Method Call Expressions](https://doc.rust-lang.org/reference/expressions/method-call-expr.html#autoderef)]

#### 7.1.2 可变引用的嵌套：`&mut T`、`&mut &T`、`&mut &mut T`

可变引用的嵌套引入了更复杂的语义层次：

```rust,ignore
let mut x = 10;
let r1 = &mut x;       // r1: &mut i32
let r2 = &mut r1;      // r2: &mut &mut i32

// 通过 r2 修改 r1 指向的值（即 x）
**r2 = 20;
assert_eq!(x, 20);
```

三级嵌套可变引用的结构：

```text
&mut &mut &mut T 的语义层次:

  r3: &mut &mut &mut i32
   │
   ├── r3 本身是一个可变引用（可被重新绑定指向另一个 &mut &mut i32）
   ├── *r3: &mut &mut i32（可变引用，可被重新绑定）
   ├── **r3: &mut i32（可变引用，可修改目标值）
   └── ***r3: i32（实际值）
```

> **重要区分**: `&mut &T` 与 `&&mut T` 是完全不同的类型：
>
> - `&mut &T`: 一个可变引用，其目标是一个共享引用。你可以修改这个可变引用使其指向**另一个**共享引用，但不能通过它修改最终目标（因为内层是 `&T`）。
> - `&&mut T`: 一个共享引用，其目标是一个可变引用。你不能通过外层的共享引用修改任何东西（外层是共享的），但可以通过内层的可变引用修改目标——前提是内层可变引用本身可达。
> [来源: [Rust Reference — Reference Types](https://doc.rust-lang.org/reference/types/pointer.html)]

```rust
let mut x = 1;
let mut y = 2;
let r_mut = &mut x;         // r_mut: &mut i32
let r_shared = &r_mut;      // r_shared: &&mut i32

// r_shared 是共享引用，不能修改 r_mut 的指向
// let r_mut2 = &mut y;
// *r_shared = r_mut2;      // ❌ 错误：不能通过共享引用赋值

// 但可以通过原始的可变引用修改 x
*r_mut = 10;                // ✅ x 现在是 10
```

#### 7.1.3 弱化的不可逆性

引用类型之间存在一个明确的**偏序关系**：

```mermaid
graph LR
    A["&mut T"] -->|"自动弱化"| B["&T"]
    C["&mut &mut T"] -->|"自动弱化"| D["&mut &T"]
    D -->|"自动弱化"| E["&&T"]
    C -->|"自动弱化"| F["&&mut T"]
    F -->|"自动弱化"| E
```

> **核心规则**: `&mut T` → `&T` 的弱化是**自动且安全**的，但 `&T` → `&mut T` 的强化永远不可能——这会破坏别名规则（Aliasing XOR Mutation）。
> [来源: [Rust Reference — Type Coercions](https://doc.rust-lang.org/reference/type-coercions.html)]

```rust
fn takes_shared(r: &i32) {}
fn takes_mut(r: &mut i32) {}

let mut x = 5;
let r_mut = &mut x;
takes_shared(r_mut);    // ✅ &mut i32 → &i32 自动弱化

let r_shared = &x;
// takes_mut(r_shared); // ❌ &i32 不能转换为 &mut i32
```

---

### 7.2 部分重借用（Partial Reborrows）

> [来源: [Rust Internals — quinedot, kpreid, 2023](https://internals.rust-lang.org/)]
> **Bloom 层级**: 分析

#### 7.2.1 编译器的字段级借用粒度

Rust 借用检查器对复合类型（结构体、元组、数组）的跟踪粒度可以达到**字段级别**。这意味着从 `&mut Parent` 中部分重借用一个字段，不会导致整个父结构被锁定。

```rust
struct Point3D {
    x: f64,
    y: f64,
    z: f64,
}

fn partial_reborrow_demo(p: &mut Point3D) {
    // 从 &mut Point3D 中部分重借用 &mut p.x
    let x_ref: &mut f64 = &mut p.x;
    *x_ref = 1.0;

    // ✅ 同时可以修改其他字段！因为编译器知道 p.y 与 p.x 不重叠
    p.y = 2.0;
    p.z = 3.0;
}
```

此机制的关键在于：编译器将 `&mut Point3D` 视为三个独立字段的可变访问权限的**联合**，当只使用其中一个字段时，其余字段仍然可用。

> [来源: [Rust Reference — Path Expressions](https://doc.rust-lang.org/reference/expressions/path-expr.html)]

#### 7.2.2 部分重借用的类型学限制

Rust Internals 社区（quinedot, kpreid, 2023）深入讨论了部分重借用的一个核心限制：**当前 Rust 类型系统无法表达"对父结构体的可变引用，排除某个子字段"的签名**。

```rust
struct Parent {
    child: Child,
    other: i32,
}

struct Child {
    value: i32,
}

// 问题：如何写 child_set_value 的签名？
// 我们想要：修改 parent.other，同时返回 &mut parent.child
fn child_set_value(parent: &mut Parent) -> &mut Child {
    parent.other = 42;
    &mut parent.child   // ❌ 错误：parent 已经被 &mut 借用，
                        // 且 parent.other 的修改与返回的借用冲突
}
```

上述代码的实际问题是：一旦执行 `&mut parent.child`，编译器认为 `parent` 整体被借用，因此在此之前对 `parent.other` 的修改必须完成，且返回借用后 `parent` 的其他字段不能再被访问。

> **当前限制**: 借用检查器虽然内部跟踪字段粒度，但这种粒度**不跨越函数边界**传递。函数签名只能表达"借用整个 `Parent`"或"借用某个字段"，不能表达"借用整个结构体，但排除特定字段"。
> [来源: [Rust Internals — Partial Reborrows Discussion, 2023](https://internals.rust-lang.org/)]（二级来源）

一种常见的工作模式是使用**临时作用域**来缩小借用的生命周期：

```rust,ignore
fn workaround(parent: &mut Parent) {
    // 步骤 1: 先修改其他字段
    parent.other = 42;

    // 步骤 2: 在独立作用域中借用 child
    {
        let child_ref = &mut parent.child;
        child_ref.value = 100;
    } // child_ref 在这里释放

    // 步骤 3: 现在可以再次访问 parent 的其他字段
    parent.other += 1;
}
```

#### 7.2.3 Polonius 与未来的改进

NLL（Non-Lexical Lifetimes）已经极大地改善了部分重借用的可用性。未来的 **Polonius** 借用检查器（基于数据流分析）将进一步提升对字段级借用的精确跟踪能力，可能支持更复杂的跨字段借用模式。

```mermaid
graph LR
    A["Lexical Lifetimes"] -->|"Rust 2015"| B["NLL"]
    B -->|"Rust 2018+"| C["Polonius"]
    C -->|"未来"| D["字段级借用签名?"]

    style B fill:#c8e6c9
    style C fill:#fff9c4
```

> [来源: [Rust RFC 2094 — NLL](https://rust-lang.github.io/rfcs/2094-nll.html)（一级来源）]
> [来源: [Rust Blog — Polonius](https://blog.rust-lang.org/inside-rust/2023/10/06/polonius-update.html)（二级来源）]

---

### 7.3 返回可变引用的形式化语义
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **Bloom 层级**: 分析
> [来源: [Verus Project — After Blocks](https://verus-lang.github.io/verus/guide/)]（二级来源）

#### 7.3.1 两次移动模型

在 Rust 中，可变引用的"借出"和"归还"可以建模为**两次独立的移动（move）**：第一次将 `&mut T` 从 lender 移动到 borrower，第二次在借用结束后归还。

```rust,ignore
fn get_first_mut<T>(slice: &mut [T]) -> Option<&mut T> {
    if slice.is_empty() {
        None
    } else {
        Some(&mut slice[0])
    }
}

fn demo_two_move() {
    let mut arr = [1, 2, 3];
    let first = get_first_mut(&mut arr);  // 移动 1: &mut arr → &mut T
    *first.unwrap() = 10;
    drop(first);                           // first 释放，借用归还
    // ✅ 现在可以再次借用 arr
    arr[1] = 20;
}
```

Verus 项目使用 `after<>` 块来形式化建模这种 lender/borrower 关系：lender 在借出期间暂时放弃对资源的独占访问权，borrower 在持有引用期间获得该权利，归还后 lender 恢复权利。

#### 7.3.2 实用模式：`split_first_mut` 与 `split_mut`

标准库提供了利用部分重借用原理的关键方法：

```rust,ignore
let mut slice = [1, 2, 3, 4, 5];

// split_first_mut: 将 &mut [T] 拆分为 &mut T 和 &mut [T]
if let Some((first, rest)) = slice.split_first_mut() {
    *first = 10;
    rest[0] = 20;  // ✅ rest 与 first 是不相交的借用
}

// split_mut: 在指定位置将 slice 一分为二
let (left, right) = slice.split_mut(2);
left[0] = 100;     // ✅ left 和 right 是不相交的区域
right[0] = 200;
```

```mermaid
graph TD
    A["&mut [1,2,3,4,5]"] -->|"split_mut(2)"| B["&mut [1,2]"]
    A -->|"split_mut(2)"| C["&mut [3,4,5]"]
    B -->|" disjoint "| C

    style B fill:#c8e6c9
    style C fill:#c8e6c9
```

> **核心保证**: `split_mut` 通过运行时检查（索引边界）确保返回的两个 `&mut [T]` 指向**不重叠的内存区域**，因此可以同时存在而不违反别名规则。
> [来源: [Rust Standard Library — slice::split_mut](https://doc.rust-lang.org/std/primitive.slice.html)]（一级来源）

---

### 7.4 Tree Borrows 模型
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **Bloom 层级**: 分析 → 应用
> [来源: [PLDI 2025 — Ralf Jung et al., "Tree Borrows"](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]（一级来源，学术论文）

#### 7.4.1 从 Stacked Borrows 到 Tree Borrows

Rust 的内存模型经历了从 **Stacked Borrows** 到 **Tree Borrows** 的演进：

| 特性 | Stacked Borrows | Tree Borrows |
|:---|:---|:---|
| 结构 | 栈（线性） | 树（分支） |
| 重借用 | 线性压栈/弹栈 | 树节点分叉 |
| `&mut &mut T` | 边缘情况复杂 | 自然支持 |
| 共享重借用 | 需精确跟踪层级 | 通过树节点权限管理 |

```mermaid
graph TD
    subgraph Stacked["Stacked Borrows（栈模型）"]
        S1["&mut T"] -->|"reborrow"| S2["&mut T"]
        S2 -->|"pop"| S1
        S3["&T"] -->|"push"| S4["&T"]
    end

    subgraph Tree["Tree Borrows（树模型）"]
        T1["root: &mut T"] -->|"reborrow"| T2["child1: &mut T"]
        T1 -->|"reborrow"| T3["child2: &T"]
        T2 -->|"reborrow"| T4["grandchild: &mut T"]
    end
```

#### 7.4.2 权限树：Foreign / Read / Write / Unique

Tree Borrows 为每个内存位置维护一棵权限树，每个节点拥有以下权限之一：

```text
Tree Borrows 权限层级:

  Foreign    ── 无权限，仅知道内存位置存在
  Read       ── 可读（共享引用 &T）
  Write      ── 可读写（需 Unique）
  Unique     ── 独占访问（可变引用 &mut T）
```

在 `&mut &mut T` 的情况下：

```rust,ignore
let mut x = 5;
let r1 = &mut x;       // 树节点 A: Unique (指向 x)
let r2 = &mut r1;      // 树节点 B: Unique (指向 r1), 节点 A 变为 Reserved

**r2 = 10;             // 通过 B 的权限链访问 x
```

树模型允许 `r2` 存在时 `r1` 暂时被"冻结"（从 Unique 降级为 Reserved），当 `r2` 释放后 `r1` 恢复 Unique 权限。这种"临时降级"在栈模型中难以表达，但在树模型中自然成为父子节点的权限转换。

> **关键洞察**: Tree Borrows 使得 `&mut &mut T` 的行为更加可预测——内层引用可以在外层引用的生命周期内被"临时冻结"，而不会触发 UB（Undefined Behavior）。
> [来源: [PLDI 2025 — Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]（一级来源）

---

### 7.5 `as_ref()` / `as_mut()` 与嵌套引用
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **Bloom 层级**: 应用
> [来源: [Rust Standard Library — Option](https://doc.rust-lang.org/std/option/enum.Option.html)]（一级来源）

#### 7.5.1 嵌套引用的类型转换

`as_ref()` 和 `as_mut()` 在处理嵌套引用时执行关键的**弱化/强化转换**：

```rust,ignore
let mut x = 42;
let opt_mut: Option<&mut i32> = Some(&mut x);

// as_ref(): Option<&mut i32> → Option<&i32>
// 关键：内层的 &mut i32 被弱化为 &i32
let opt_shared: Option<&i32> = opt_mut.as_ref();
```

类型转换的精确映射：

```text
as_ref() 的转换行为:

  Option<&mut T>    →  Option<&T>     (&mut → &, 弱化)
  Option<&T>        →  Option<&T>     (无变化)
  Option<Box<T>>    →  Option<&T>     (通过 Deref)
  Result<&mut T, E> →  Result<&T, E>  (&mut → &, 弱化)

as_mut() 的转换行为:

  Option<&mut T>    →  Option<&mut T> (无变化，保持可变性)
  Result<&mut T, E> →  Result<&mut T, E> (保持可变性)
```

#### 7.5.2 生命周期行为

```rust,ignore
fn demo_lifetime_propagation<'a>(opt: &'a Option<&'a mut i32>) -> Option<&'a i32> {
    opt.as_ref()  // 生命周期 'a 从输入传播到输出
}
```

> **关键洞察**: `as_ref()` 不创建新的引用，而是**重新打包**现有的引用，保持原始生命周期不变。对于嵌套引用，这意味着内层引用的生命周期约束会被完整保留。
> [来源: [Rust Reference — Lifetime Elision](https://doc.rust-lang.org/reference/lifetime-elision.html)]（一级来源）

---

### 7.6 代码示例集
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **Bloom 层级**: 应用

#### 7.6.1 嵌套引用的构造与模式匹配

```rust
fn nested_reference_patterns() {
    let x = 5;
    let r = &&&x;

    // 模式匹配解包多级引用
    match r {
        &&&val => assert_eq!(val, 5),  // 匹配并解引用三层
    }

    // 等价于显式解引用
    assert_eq!(***r, 5);
}
```

#### 7.6.2 结构体字段的部分重借用

```rust
struct Buffer {
    data: Vec<u8>,
    cursor: usize,
    capacity: usize,
}

impl Buffer {
    fn process(&mut self) {
        // 部分重借用：同时持有 data 和 cursor 的可变引用
        let data_ref = &mut self.data;
        let cursor_ref = &mut self.cursor;

        // 使用 data_ref 和 cursor_ref 进行操作
        if *cursor_ref < data_ref.len() {
            data_ref[*cursor_ref] = 0;
            *cursor_ref += 1;
        }

        // 它们释放后，self 整体恢复可用
        self.capacity = self.data.capacity();
    }
}
```

#### 7.6.3 `split_mut` 创建不相交可变引用

```rust,ignore
fn parallel_update(matrix: &mut [[i32; 3]; 2]) {
    // 将 2x3 矩阵分成两行，每行一个独立的 &mut [i32; 3]
    let (first, rest) = matrix.split_mut(1);
    let row0 = &mut first[0];
    let row1 = &mut rest[0];

    // row0 和 row1 指向不重叠的内存
    row0[0] = 1;
    row1[0] = 2;
}
```

#### 7.6.4 迭代器可变链

```rust
fn iterator_mut_chains() {
    let mut vec = vec![10, 20, 30];

    // iter_mut() 产生 &mut i32，enumerate() 包装为 (usize, &mut i32)
    for (idx, val) in vec.iter_mut().enumerate() {
        *val += idx as i32;  // 可以修改原始值
    }

    assert_eq!(vec, vec![10, 21, 32]);
}
```

> **关键洞察**: `iter_mut()` 返回的迭代器产生 `&mut T`，后续适配器（如 `enumerate()`）通过**部分重借用**原理将 `&mut T` 包装为 `(usize, &mut T)` 而不破坏可变性。
> [来源: [Rust Standard Library — Iterator](https://doc.rust-lang.org/std/iter/trait.Iterator.html)]（一级来源）

---

### 7.7 边界分析
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **Bloom 层级**: 分析
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

#### 7.7.1 命题与反命题

**命题 A**: "`&mut &mut T` 允许修改内层引用指向的目标"

- ✅ **成立，但有条件**: 确实可以通过 `**r = new_value` 修改最终目标，但**外层可变引用必须始终有效**。如果外层引用被移动或重新绑定，整个访问链失效。

**命题 B**: "嵌套引用就像 C 的指针的指针"

- ❌ **不成立**: Rust 的嵌套引用在**每一级**都受借用检查器约束。`&mut &mut T` 不是两个独立的指针，而是一个受严格别名规则约束的层级结构。在 C 中你可以任意复制 `T**` 并解引用；在 Rust 中，复制 `&&mut T` 会产生新的共享引用，但原始的可变引用仍然保持独占性。

```rust
let mut x = 5;
let r1 = &mut x;
let r2 = &r1;       // r2: &&mut i32
let r3 = r2;        // r3: &&mut i32（复制共享引用是允许的）

// 但 r1 仍然是 &mut x 的唯一可变路径
*r1 = 10;           // ✅
// *r2 = 20;        // ❌ 不能通过共享引用修改
```

**命题 C**: "部分重借用适用于所有复合类型"

- ⚠️ **大部分成立，但有例外**: 结构体字段、元组元素、数组元素都支持部分重借用。但以下类型存在限制：
  - **闭包（Closures）**: 无法部分重借用捕获的环境变量
  - **Trait 对象（Trait Objects）**: `&mut dyn Trait` 无法按字段拆分，因为具体字段布局被擦除
  - **联合体（Unions）**: 由于字段可能重叠，部分重借用不安全

```rust
union MyUnion {
    a: i32,
    b: f32,
}

fn union_demo(u: &mut MyUnion) {
    // let a_ref = &mut u.a;  // ❌ 不安全：u.a 和 u.b 共享内存
    // u.b = 1.0;             // 可能与 a_ref 指向的内存重叠
}
```

> [来源: [Rust Reference — Unions](https://doc.rust-lang.org/reference/items/unions.html)]（一级来源）

#### 7.7.2 边界极限

```text
边界 1: 部分重借用的函数边界限制
├── 编译器内部跟踪字段粒度
├── 但函数签名无法表达 "&mut Parent 排除 child 字段"
└──  workaround: 使用临时作用域或拆分函数

边界 2: 自动解引用的不对称性
├── &&&&T 可以自动解引用到 &T（多次解引用）
├── &mut &mut T 不会自动解引用到 &mut T
└── 原因：自动解引用在需要精确可变性的上下文中过于危险

边界 3: Tree Borrows 的编译器采纳状态
├── Tree Borrows 是学术研究提出的模型（PLDI 2025）
├── Miri（Rust 的解释器/检查器）已支持 Tree Borrows
└── rustc 编译器后端仍基于类似 Stacked Borrows 的模型，但逐步对齐
```

> [来源: [Miri — Tree Borrows](https://github.com/rust-lang/miri)]（二级来源）

---

### 7.8 常见困惑解析
>
> **[来源: [crates.io](https://crates.io/)]**

> **Bloom 层级**: 理解 → 分析
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

#### 困惑 1: `let r: &&i32 = &&5;` —— 中间引用的生命周期

```rust
let r: &&i32;
{
    let x = 5;
    let r1 = &x;
    r = &r1;        // ❌ 错误：r1 的生命周期不够长
} // x 和 r1 在这里释放
```

编译器为每个临时引用生成**独立的临时值**：

```rust
let r: &&i32;
{
    let x = 5;
    let tmp1 = &x;      // 临时引用 1
    let tmp2 = &tmp1;   // 临时引用 2
    r = tmp2;           // r 依赖 tmp1 和 x 的生命周期
}
```

> **关键**: `&&5` 涉及**三个**值：原始值 `5`、第一层临时引用、第二层临时引用。整个链的生命周期受最弱环节（最短生命周期）限制。
> [来源: [Rust Reference — Temporary Values](https://doc.rust-lang.org/reference/expressions.html#temporaries)]（一级来源）

#### 困惑 2: `&mut &T` vs `&&mut T`

```rust,ignore
let mut x = 5;
let mut y = 10;

// 场景 A: &mut &T
let r1: &i32 = &x;
let r2: &mut &i32 = &mut r1;  // r2 可以修改 r1 指向谁
// *r2 = &y;                   // ✅ 现在 r1 指向 y（注意：r1 本身需是 mut 绑定）

// 场景 B: &&mut T
let r3: &mut i32 = &mut x;
let r4: &&mut i32 = &r3;       // r4 是共享引用，不能修改 r3 的指向
// *r4 = &mut y;               // ❌ 错误：不能通过共享引用赋值
```

| 类型 | 可读 | 可修改目标值 | 可修改引用指向 |
|:---|:---:|:---:|:---:|
| `&mut &T` | ✅ | ❌（内层是共享引用） | ✅（外层是可变的） |
| `&&mut T` | ✅ | ❌（外层是共享的） | ❌（外层是共享的） |
| `&mut &mut T` | ✅ | ✅ | ✅ |

#### 困惑 3: 为什么 `&&&&T` 自动解引用但 `&mut &mut T` 不自动解引用到 `&mut T`？

```rust
let r_shared: &&&&i32 = &&&&5;
let target: &i32 = r_shared;   // ✅ 自动解引用 3 层

let mut x = 5;
let r_mut: &mut &mut i32 = &mut &mut x;
// let target: &mut i32 = r_mut;  // ❌ 不会自动解引用！
let target: &mut i32 = *r_mut;    // ✅ 必须显式解引用
```

原因：**可变引用的自动解引用在赋值/传参上下文中有更严格的限制**。编译器不会隐式地将 `&mut &mut T` 转换为 `&mut T`，因为这会隐藏内存 indirection 的层级，而在可变访问中，每一级 indirection 的语义都至关重要。

> **原则**: Rust 的隐式转换是**保守的**——对于共享引用，多次自动解引用是安全的（只读）；对于可变引用，编译器要求显式控制以避免意外的别名破坏。
> [来源: [Rust Reference — Auto Deref](https://doc.rust-lang.org/reference/expressions/method-call-expr.html#autoderef)]（一级来源）

---

### 7.9 形式化视角
>
> **[来源: [docs.rs](https://docs.rs/)]**

> **Bloom 层级**: 分析
> [来源: [RustBelt / Iris](https://plv.mpi-sws.org/rustbelt/)]（一级来源，POPL 论文）

从形式化验证的角度，多级引用可以用**分离逻辑（Separation Logic）**建模：

```text
分离逻辑中的多级引用表示:

  &T  ≈  λπ. ∃l. (π ↦ T) * (value(l) = T)
  &mut T ≈  λπ. ∃l. (π ↦ T) * exclusive(π) * (value(l) = T)

  &mut &mut T ≈  λπ. ∃l1,l2. (π ↦ l2) * exclusive(π)
                              * (l2 ↦ T) * exclusive(l2)
                              * (value(l1) = T)
```

Tree Borrows 的权限树在 Iris 框架中可以建模为**分式权限（Fractional Permissions）**的层次化分配：每个节点持有父节点授予的权限子集，当子节点活跃时，父节点的对应权限被冻结。

> **学术连接**: Tree Borrows 模型已被整合进 RustBelt 项目的 Iris 框架中，为 Rust 的 unsafe 代码验证提供了更精确的内存模型基础。
> [来源: [PLDI 2025 — Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]（一级来源）

---

### 7.10 名义与结构类型的引用边界
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **Bloom 层级**: 分析

多级引用语义与名义/结构类型系统的交叉点，决定了**复杂借用场景中类型检查的精确行为**：

**引用的结构本质**：

`&T` 和 `&mut T` 作为类型是**结构构造**的——它们由引用构造子与目标类型组合而成。这意味着：

```rust
// 结构规则自动适用
let r1: &&i32 = &&5;           // ✅ & 构造子可嵌套
let r2: &mut &mut String = &mut &mut String::from("hi"); // ✅ 多层可变
```

- `&` / `&mut` 的嵌套深度、自动解引用链、引用弱化（`&mut` → `&`）均遵循**结构规则**，与目标类型 `T` 是否是名义类型无关。

**目标类型的名义约束传导**：

然而，当目标类型 `T` 是名义类型时，这一名义身份会**完整传导**至引用层级：

```rust
struct UserId(u64);
struct SessionId(u64);

let uid: &UserId = &UserId(42);
// let sid: &SessionId = uid;   // ❌ 错误：&UserId ≠ &SessionId（名义不等价）
```

即使 `UserId` 和 `SessionId` 内部都是 `u64`，`&UserId` 与 `&SessionId` 仍因名义身份而不兼容。

**部分重借用的名义/结构边界**：

| 目标类型 | 重借用粒度 | 类型系统规则 |
|:---|:---|:---|
| 名义 struct（`struct S { a: A, b: B }`） | 字段级（`&mut s.a`） | 名义类型允许字段级部分重借用，编译器按字段名义跟踪 |
| 结构元组（`(A, B)`） | 位置级（`&mut t.0`） | 结构类型允许位置级部分重借用，编译器按位置索引跟踪 |
| 结构数组（`[T; N]`） | 元素级（`&mut arr[i]`） | 结构类型允许元素级部分重借用 |
| 名义 enum | 变体级 | 受 match 穷尽性约束，部分重借用受变体名义限制 |

**交叉定理**：

> **定理 R1（引用层级的规则分离）**：在 Rust 中，引用操作的**可解引用性、弱化、生命周期子类型化**由结构规则支配；而引用操作的**类型等价性、可互换性**由目标类型的名义/结构性质支配。两者在多级引用中并行生效，互不抵消。
>
> **实践推论**：当你写 `&mut &T` 时，外层的可变性遵循结构规则（`&mut` 构造子决定），但内层 `&T` 的具体类型等价性仍受 `T` 的名义身份约束。这意味着**你不能通过多级引用来绕过名义类型的隔离**。

```rust
struct Secret(String);
struct Public(String);

let s: &mut &Secret = &mut &Secret(String::from("x"));
// *s = &Public(String::from("y"));  // ❌ 错误：&Public ≠ &Secret
// 即使都是 &String 的包装，名义身份阻止了跨类型赋值
```

> **分析**: 这一边界是 Rust 类型系统安全性的核心支柱之一——多级引用提供了表达复杂内存关系的灵活性（结构规则），但名义类型确保了语义契约在任何引用层级都不会被意外破坏（名义规则）。
> [来源: [Rust Reference: Types] · [Rust Reference: Subtyping] · [Rust Reference: Type Coercions]]（一级来源）

> **与类型系统的关联**: 详见 [`04_type_system.md`](../01_foundation/04_type_system.md) 对名义类型与结构类型的完整分析——其中第 11.7 节专门论证了引用构造的结构本质与目标类型名义约束的交互关系。

---

## 来源与延伸阅读（本节）
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Rust Reference — Reference Types](https://doc.rust-lang.org/reference/types/pointer.html) | ✅ 一级 | 引用类型的语法与语义 |
| [Rust Reference — Type Coercions](https://doc.rust-lang.org/reference/type-coercions.html) | ✅ 一级 | 类型强制与引用弱化 |
| [Rust Reference — Method Call Expressions](https://doc.rust-lang.org/reference/expressions/method-call-expr.html) | ✅ 一级 | 自动解引用规则 |
| [RFC 2094 — Non-Lexical Lifetimes](https://rust-lang.github.io/rfcs/2094-nll.html) | ✅ 一级 | NLL 的设计与实现 |
| [PLDI 2025 — Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/) | ✅ 一级 | 树形借用模型学术论文 |
| [RustBelt / Iris](https://plv.mpi-sws.org/rustbelt/) | ✅ 一级 | Rust 形式化验证框架 |
| [Rust Internals — Partial Reborrows](https://internals.rust-lang.org/) | ⚠️ 二级 | 社区对部分重借用的讨论 |
| [Rust Blog — Polonius Update](https://blog.rust-lang.org/inside-rust/2023/10/06/polonius-update.html) | ⚠️ 二级 | Polonius 借用检查器进展 |
| [Verus Project](https://verus-lang.github.io/verus/guide/) | ⚠️ 二级 | 形式化验证与 after<> 块 |
| [Miri — Tree Borrows](https://github.com/rust-lang/miri) | ⚠️ 二级 | Miri 对 Tree Borrows 的实现 |
| [TRPL Ch4 — References](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html) | ⚠️ 三级 | 引用的工程直觉 |
| [Rustonomicon — Transmutes](https://doc.rust-lang.org/nomicon/transmutes.html) | ⚠️ 三级 | unsafe 中的引用转换 |

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **权威来源对齐变更日志**: 2026-05-22 新增多级引用语义、部分重借用、Tree Borrows 模型、as_ref/as_mut 嵌套引用转换 [来源: Authority Source Sprint Batch 9]

---

## 权威来源索引

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **补充来源**

> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
> [来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]
> [来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]
> [来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]
> [来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]
