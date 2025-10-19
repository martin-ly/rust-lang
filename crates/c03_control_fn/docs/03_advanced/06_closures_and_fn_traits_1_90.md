# 06. 闭包与 Fn* 特征 (Closures & Fn Traits - Rust 1.90)

> **文档类型**：高级  
> **难度等级**：⭐⭐⭐⭐  
> **预计阅读时间**：2小时  
> **前置知识**：闭包基础、trait 系统、所有权与借用

## 📖 内容概述

本文档系统讲解闭包的捕获语义、类型推断、Fn/FnMut/FnOnce 三类调用特征、move 语义、生命周期约束与常见陷阱，并提供工程化实践建议。

## 🎯 学习目标

完成本文档学习后，你将能够：

- [ ] 理解闭包的三种捕获模式
- [ ] 掌握 Fn/FnMut/FnOnce trait 的区别和选择
- [ ] 使用 move 闭包转移所有权
- [ ] 理解闭包的生命周期约束
- [ ] 解决闭包相关的常见问题
- [ ] 设计高效的高阶函数 API

## 📚 目录

- [06. 闭包与 Fn\* 特征 (Closures \& Fn Traits - Rust 1.90)](#06-闭包与-fn-特征-closures--fn-traits---rust-190)
  - [📖 内容概述](#-内容概述)
  - [🎯 学习目标](#-学习目标)
  - [📚 目录](#-目录)
  - [6.1. 捕获与三类调用特征](#61-捕获与三类调用特征)
  - [`move` 闭包](#move-闭包)
  - [返回闭包与 impl Trait](#返回闭包与-impl-trait)
  - [捕获推导与借用规则](#捕获推导与借用规则)
  - [常见陷阱](#常见陷阱)

---

## 6.1. 捕获与三类调用特征

- 根据闭包体对环境变量的使用方式，编译器自动推断为：
  - `Fn`：仅借用不可变引用；
  - `FnMut`：需要可变借用；
  - `FnOnce`：发生所有权移动（消耗环境）。

```rust
fn call_fn<F: Fn()>(f: F) { f(); }
fn call_fnmut<F: FnMut()>(mut f: F) { f(); }
fn call_fnonce<F: FnOnce()>(f: F) { f(); }

fn demo() {
    let x = 1;
    call_fn(|| println!("read-only: {}", x));

    let mut y = 0;
    call_fnmut(|| y += 1);

    let s = String::from("hi");
    call_fnonce(|| drop(s)); // 移动所有权，闭包为 FnOnce
}
```

## `move` 闭包

- `move` 强制按值捕获（或复制/克隆），常用于跨线程/异步。

```rust
fn spawn_thread() {
    let data = String::from("msg");
    std::thread::spawn(move || {
        println!("{}", data);
    }).join().unwrap();
}
```

## 返回闭包与 impl Trait

```rust
fn make_adder(delta: i32) -> impl Fn(i32) -> i32 {
    move |x| x + delta
}
```

## 捕获推导与借用规则

- 按需最小捕获：仅捕获用到的字段（Rust 1.90 稳定）。
- 与借用规则一致：同时存在可变与不可变借用将报错；`move` 后原变量不再可用（或变为部分可用）。

## 常见陷阱

- 闭包存储在 `Box<dyn Fn...>` 时涉及对象安全与生命周期；
- 在循环中捕获迭代变量要注意所有权；
- `async` 闭包目前需要显式写法（如 `async move |x| { ... }`）。

---

工程建议：

- 以函数边界为准选择 `Fn`/`FnMut`/`FnOnce` 约束；
- 在线程/异步场景优先使用 `move` 闭包；
- 对外接口尽可能返回 `impl Fn...` 或泛型参数以获得静态分发性能。
