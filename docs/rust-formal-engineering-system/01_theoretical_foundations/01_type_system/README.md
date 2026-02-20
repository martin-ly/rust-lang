# 类型系统理论

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> 内容已整合至： [type_theory/](../../../research_notes/type_theory/)

- [类型系统基础](../../../research_notes/type_theory/type_system_foundations.md)
- [Trait 系统形式化](../../../research_notes/type_theory/trait_system_formalization.md)
- [型变理论](../../../research_notes/type_theory/variance_theory.md)
- [生命周期形式化](../../../research_notes/formal_methods/lifetime_formalization.md)

[返回主索引](../../00_master_index.md)

---

## 形式化链接

| 文档 | 路径 | 内容 |
| :--- | :--- | :--- |
| **类型系统基础** | [../../../research_notes/type_theory/type_system_foundations.md](../../../research_notes/type_theory/type_system_foundations.md) | Curry-Howard 对应、类型推导算法 |
| **Trait 系统形式化** | [../../../research_notes/type_theory/trait_system_formalization.md](../../../research_notes/type_theory/trait_system_formalization.md) | 类型类、关联类型、Orphan 规则 |
| **型变理论** | [../../../research_notes/type_theory/variance_theory.md](../../../research_notes/type_theory/variance_theory.md) | 型变规则证明、类型构造器 |
| **生命周期形式化** | [../../../research_notes/formal_methods/lifetime_formalization.md](../../../research_notes/formal_methods/lifetime_formalization.md) | 生命周期作为区域、子类型关系 |
| **证明索引** | [../../../research_notes/PROOF_INDEX.md](../../../research_notes/PROOF_INDEX.md) | 类型安全相关证明 |
| **工具指南** | [../../../research_notes/TOOLS_GUIDE.md](../../../research_notes/TOOLS_GUIDE.md) | 类型验证工具使用 |

---

## 类型系统核心概念

### 类型即命题（Curry-Howard 对应）

在 Rust 类型系统中，类型对应于逻辑命题，程序对应于证明：

```rust
// 简单类型对应真值
// () : 单位类型 = 真（True）
// !  :  never 类型 = 假（False，逻辑矛盾）

// 积类型（Product Type）对应逻辑与
// (A, B) 对应 A ∧ B
fn pair_type() -> (i32, String) {
    (42, String::from("hello"))  // 证明 42 ∧ "hello"
}

// 和类型（Sum Type）对应逻辑或
// Result<A, B> 对应 A ∨ B
fn sum_type() -> Result<i32, String> {
    Ok(42)  // 证明左支：存在 i32
    // Err("error".to_string())  // 或右支：存在 String
}

// 函数类型对应逻辑蕴含
// A -> B 对应 A → B
fn implication(x: i32) -> String {
    x.to_string()  // 给定 i32，可以构造 String
}
```

### 泛型与参数多态

```rust
// 全称量词（∀）的 Rust 表达
// id :: ∀a. a -> a
fn id<T>(x: T) -> T {
    x
}

// 约束全称量词
// show :: ∀a. Show a => a -> String
fn show<T: ToString>(x: T) -> String {
    x.to_string()
}

// 高阶类型（类型构造器）
// Vec : Type -> Type
// Vec<i32> : Type
struct Container<T>(Vec<T>);

// 关联类型（类型族）
trait ContainerTrait {
    type Item;  // 关联类型
    fn get(&self) -> Option<&Self::Item>;
}

impl<T> ContainerTrait for Container<T> {
    type Item = T;
    fn get(&self) -> Option<&T> {
        self.0.first()
    }
}
```

### 型变（Variance）

型变描述复合类型如何随其组件类型的子类型关系变化：

```rust
// 协变（Covariant）：保持子类型方向
// &'a T 对于 'a 和 T 都是协变的
fn covariance<'a, 'b: 'a>(x: &'b str) -> &'a str {
    x  // 'b <: 'a 意味着 &'b str <: &'a str
}

// 逆变（Contravariant）：反转子类型方向
// fn(T) -> U 对于 T 是逆变的
fn contravariance<F>(f: F)
where
    F: Fn(&'static str),  // 接受 &'static str
{
    let s: &str = "hello";
    f(s);  // 可以传入生命周期更短的引用
}

// 不变（Invariant）：无子类型关系
// &mut T 对于 T 是不变的
fn invariance(x: &mut &'static str) {
    // x 只能接受 &'static str，不能接受 &str
}

// 类型构造器的型变
// Vec<T> : 对 T 协变
// Cell<T> : 对 T 不变
// fn(T) -> U : 对 T 逆变，对 U 协变
```

### 类型推导

```rust
// Hindley-Milner 类型推导的 Rust 实现
// 编译器自动推断最一般的类型

fn type_inference() {
    let x = 5;           // 推断为 i32（默认整数类型）
    let y = vec![x];     // 推断为 Vec<i32>
    let z = &y;          // 推断为 &Vec<i32>

    // 泛型函数的类型推导
    let id_result = id(x);  // T 被实例化为 i32

    // 闭包类型推导
    let add = |a, b| a + b;  // 推断为 impl Fn(i32, i32) -> i32
    let sum = add(1, 2);
}

// 显式类型标注与推导结合
fn mixed_inference<T: Default>(items: &[T]) -> Vec<T> {
    let mut result = Vec::new();  // 推断为 Vec<T>
    for item in items {
        result.push(T::default());
    }
    result
}
```

### 类型安全保证

```rust
// 类型系统防止的操作
// 以下代码无法编译（故意注释掉）

fn type_safety() {
    let x: i32 = 5;
    // let y: String = x;  // 错误：类型不匹配

    let v = vec![1, 2, 3];
    // let s: String = v;  // 错误：类型不匹配

    // 空指针安全
    let opt: Option<i32> = Some(5);
    // let val = opt + 1;  // 错误：Option<i32> 不能加 i32

    match opt {
        Some(val) => println!("{}", val + 1),  // 正确：在匹配分支中解包
        None => println!("No value"),
    }
}
```
