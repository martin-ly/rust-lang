# 1.1.3 Rust复合类型语义深度分析

## 📊 目录

- [1.1.3 Rust复合类型语义深度分析](#113-rust复合类型语义深度分析)
  - [📊 目录](#-目录)
  - [1.1.3.1 复合类型理论基础](#1131-复合类型理论基础)
    - [1.1.3.1.1 结构体与枚举](#11311-结构体与枚举)
    - [1.1.3.1.2 内存布局与优化](#11312-内存布局与优化)
  - [相关文档推荐](#相关文档推荐)
  - [知识网络节点](#知识网络节点)
  - [自动化验证脚本](#自动化验证脚本)
  - [工程案例](#工程案例)
  - [典型反例](#典型反例)
  - [1.1.3.2 复合类型与所有权、生命周期、trait对象安全](#1132-复合类型与所有权生命周期trait对象安全)
    - [1.1.3.2.1 复合类型与所有权转移](#11321-复合类型与所有权转移)
    - [1.1.3.2.2 复合类型与生命周期推断](#11322-复合类型与生命周期推断)
    - [1.1.3.2.3 trait对象在复合类型中的安全性](#11323-trait对象在复合类型中的安全性)
  - [复杂工程案例](#复杂工程案例)
  - [递归扩展自动化验证脚本](#递归扩展自动化验证脚本)
  - [递归扩展反例库](#递归扩展反例库)
  - [递归扩展交叉借用](#递归扩展交叉借用)

**文档版本**: V1.0  
**创建日期**: 2025-01-27  
**所属层**: 基础语义层 (Foundation Semantics Layer)  
**学术等级**: 专家级 (Expert Level)  

---

## 1.1.3.1 复合类型理论基础

### 1.1.3.1.1 结构体与枚举

- 结构体（struct）和枚举（enum）是Rust复合类型的核心。
- 支持嵌套、泛型、trait实现。

### 1.1.3.1.2 内存布局与优化

- 复合类型的内存布局影响性能与安全。
- 支持repr(C)、repr(packed)等属性。

---

## 相关文档推荐

- [04_generic_semantics.md] 泛型与复合类型
- [15_memory_layout_semantics.md] 内存布局与复合类型
- [08_trait_system_semantics.md] trait与复合类型
- [16_unsafe_boundary_semantics.md] Unsafe与复合类型

## 知识网络节点

- 所属层级：基础语义层-复合类型分支
- 上游理论：类型系统、泛型
- 下游理论：内存布局、trait实现、Unsafe边界
- 交叉节点：泛型、trait、内存模型

---

## 自动化验证脚本

```rust
// Rust自动化测试：结构体大小与对齐
# [repr(C)]
struct Pair {
    a: u8,
    b: u32,
}

fn main() {
    assert_eq!(std::mem::size_of::<Pair>(), 8);
    assert_eq!(std::mem::align_of::<Pair>(), 4);
}
```

## 工程案例

```rust
// 标准库Option复合类型优化
let x: Option<&u8> = None;
assert_eq!(std::mem::size_of::<Option<&u8>>(), std::mem::size_of::<&u8>());

// 枚举与结构体组合
enum MyEnum {
    A(i32),
    B { x: f64, y: f64 },
}
```

## 典型反例

```rust
// 非对齐访问反例
# [repr(packed)]
struct Bad {
    a: u8,
    b: u32,
}

fn main() {
    let s = Bad { a: 1, b: 2 };
    let pb = &s.b as *const u32;
    unsafe { println!("{}", *pb); } // 可能未定义行为
}
```

---

## 1.1.3.2 复合类型与所有权、生命周期、trait对象安全

### 1.1.3.2.1 复合类型与所有权转移

- 结构体和枚举的所有权转移遵循Rust所有权语义。
- 嵌套结构体的所有权递归转移，Drop顺序与字段声明逆序。

### 1.1.3.2.2 复合类型与生命周期推断

- 结构体字段可带生命周期参数，自动推断借用安全。
- 枚举变体中借用字段的生命周期需统一。

### 1.1.3.2.3 trait对象在复合类型中的安全性

- 结构体/枚举可包含trait对象字段，需满足对象安全。
- trait对象字段影响内存布局和动态分发。

---

## 复杂工程案例

```rust
// 嵌套结构体与所有权转移
struct Inner { data: String }
struct Outer { inner: Inner, value: i32 }

fn move_outer(o: Outer) -> String {
    o.inner.data // 所有权递归转移
}

// 泛型复合类型与生命周期
struct RefHolder<'a, T> { r: &'a T }

fn get_ref<'a, T>(v: &'a T) -> RefHolder<'a, T> {
    RefHolder { r: v }
}

// trait对象在结构体中的用法
trait Draw { fn draw(&self); }
struct Widget { comp: Box<dyn Draw> }

impl Draw for i32 { fn draw(&self) { println!("draw {}", self); } }

fn main() {
    let w = Widget { comp: Box::new(42) };
    w.comp.draw();
}
```

---

## 递归扩展自动化验证脚本

```rust
// 联合体（union）安全性自动化测试
union MyUnion {
    i: i32,
    f: f32,
}

fn main() {
    let u = MyUnion { i: 42 };
    unsafe { assert_eq!(u.i, 42); }
}

// 枚举tag内存布局自动化测试
# [repr(u8)]
enum MyEnum { A = 1, B = 2 }
fn main2() {
    assert_eq!(std::mem::size_of::<MyEnum>(), 1);
}
```

---

## 递归扩展反例库

```rust
// 未初始化联合体反例
union BadUnion { i: i32, f: f32 }
fn bad_union() {
    let u: BadUnion = unsafe { std::mem::MaybeUninit::uninit().assume_init() };
    // unsafe { println!("{}", u.i); } // UB: 读取未初始化字段
}

// 枚举未覆盖反例
fn match_enum(e: MyEnum) -> u8 {
    match e {
        MyEnum::A => 1,
        // MyEnum::B 未覆盖，若加新变体会导致非穷尽匹配
    }
}
```

---

## 递归扩展交叉借用

- [02_ownership_semantics.md] 所有权转移与复合类型
- [06_lifetime_semantics.md] 生命周期与复合类型
- [08_trait_system_semantics.md] trait对象安全
- [16_unsafe_boundary_semantics.md] 联合体与Unsafe边界
