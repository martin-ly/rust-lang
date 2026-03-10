# 闭包速查卡 (Closures Cheatsheet)

> **最后更新**: 2026-03-08
> **Rust 版本**: 1.94.0+

---

## 闭包基础

### 定义闭包

```rust
// 基本闭包
let add = |a, b| a + b;

// 带类型的闭包
let multiply: fn(i32, i32) -> i32 = |a, b| a * b;

// 多行闭包
let greet = |name| {
    let greeting = format!("Hello, {}!", name);
    println!("{}", greeting);
    greeting
};
```

### 捕获环境

```rust
let x = 10;

// 不可变借用捕获
let closure = || println!("x = {}", x);

// 可变借用捕获
let mut y = 5;
let mut closure = || {
    y += 1;
    println!("y = {}", y);
};

// 移动捕获
let s = String::from("hello");
let closure = move || println!("{}", s);
```

---

## 闭包 Trait

| Trait | 描述 | 使用场景 |
|-------|------|----------|
| `Fn` | 不可变借用捕获 | 可多次调用 |
| `FnMut` | 可变借用捕获 | 可多次调用，需要可变引用 |
| `FnOnce` | 移动捕获 | 只能调用一次 |

### Trait 使用示例

```rust
fn apply_fn<F>(f: F, x: i32) -> i32
where
    F: Fn(i32) -> i32,
{
    f(x)
}

fn apply_fn_mut<F>(mut f: F, x: i32) -> i32
where
    F: FnMut(i32) -> i32,
{
    f(x)
}

fn apply_fn_once<F>(f: F, x: i32) -> i32
where
    F: FnOnce(i32) -> i32,
{
    f(x)
}
```

---

## 常见用法

### 迭代器方法

```rust
let nums = vec![1, 2, 3, 4, 5];

// map
let doubled: Vec<i32> = nums.iter().map(|x| x * 2).collect();

// filter
let evens: Vec<&i32> = nums.iter().filter(|x| *x % 2 == 0).collect();

// fold
let sum = nums.iter().fold(0, |acc, x| acc + x);
```

### 高阶函数

```rust
fn compose<F, G, T>(f: F, g: G) -> impl Fn(T) -> T
where
    F: Fn(T) -> T,
    G: Fn(T) -> T,
    T: Copy,
{
    move |x| f(g(x))
}
```

---

## 相关文档

- [控制流与函数速查卡](./control_flow_functions_cheatsheet.md)
- [迭代器速查卡](./collections_iterators_cheatsheet.md)
- [类型系统速查卡](./type_system.md)
