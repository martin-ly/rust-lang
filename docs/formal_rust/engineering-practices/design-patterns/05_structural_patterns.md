# 结构型模式集


## 📊 目录

- [1. 适配器模式](#1-适配器模式)
  - [1.1 trait适配器](#11-trait适配器)
- [2. 装饰器与外观](#2-装饰器与外观)
  - [2.1 装饰器实现](#21-装饰器实现)
- [3. 组合与代理](#3-组合与代理)
  - [3.1 组合模式](#31-组合模式)
- [4. 新类型与包装](#4-新类型与包装)
  - [4.1 newtype包装](#41-newtype包装)
- [5. 批判性分析与未来展望](#5-批判性分析与未来展望)


## 1. 适配器模式

- trait适配、From/Into、Deref/DerefMut

### 1.1 trait适配器

```rust
trait Target { fn request(&self); }
struct Adaptee;
impl Adaptee { fn specific_request(&self) { /* ... */ } }
struct Adapter<'a> { adaptee: &'a Adaptee }
impl<'a> Target for Adapter<'a> { fn request(&self) { self.adaptee.specific_request(); } }
```

## 2. 装饰器与外观

- newtype包装、宏自动生成、Facade简化接口

### 2.1 装饰器实现

```rust
struct Logger<T> { inner: T }
impl<T: Target> Target for Logger<T> { fn request(&self) { println!("log"); self.inner.request(); } }
```

## 3. 组合与代理

- 组合模式（树形结构）、代理模式（访问控制、缓存）

### 3.1 组合模式

```rust
trait Component { fn operation(&self); }
struct Leaf; struct Composite { children: Vec<Box<dyn Component>> }
impl Component for Leaf { fn operation(&self) { /* ... */ } }
impl Component for Composite { fn operation(&self) { for c in &self.children { c.operation(); } } }
```

## 4. 新类型与包装

- newtype语义包装、单位类型、类型安全

### 4.1 newtype包装

```rust
struct UserId(u64);
fn get_user(id: UserId) { /* ... */ }
```

## 5. 批判性分析与未来展望

- Rust结构型模式强调类型安全与组合性，trait与宏提升灵活性，但复杂组合带来类型推导难题
- 未来可探索自动化装饰器/代理生成与类型安全组合
