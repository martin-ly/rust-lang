# 教程：理解生命周期

> **创建日期**: 2026-02-24
> **目标受众**: 初学者-进阶
> **预计阅读时间**: 20分钟
> **级别**: L1/L2

---

## 引言

生命周期是Rust最令初学者困惑的概念之一。但其实它的核心思想很简单：**引用不能比它指向的数据活得更长**。

---

## 第一部分：什么是生命周期？

### 直观理解

生命周期就是引用的**有效期限**。

```rust
{
    let x = 5;           // x的生命周期开始
    let r = &x;          // r借用x，r的生命周期不能超过x
    println!("{}", r);   // r在此使用
}  // x和r的生命周期结束
```

### 为什么需要生命周期？

防止悬垂引用：

```rust
let r;
{
    let x = 5;
    r = &x;  // 错误！x在块结束时被释放
}
// r仍然有效，但指向无效内存
```

---

## 第二部分：生命周期语法

### 显式生命周期

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// 'a 是一个生命周期参数
// 表示x、y和返回值都有相同的生命周期
```

### 生命周期省略

大多数情况下，编译器自动推断：

```rust
fn first_word(s: &str) -> &str { ... }

// 编译器自动添加：
// fn first_word<'a>(s: &'a str) -> &'a str
```

**三条省略规则**:

1. 每个引用参数有自己的生命周期
2. 只有一个输入生命周期 → 赋给输出
3. `&self`存在 → `self`的生命周期赋给输出

---

## 第三部分：生命周期关系

### 'static 生命周期

```rust
let s: &'static str = "hello";

// 'static 表示整个程序运行期间有效
// 字符串字面量是'static
```

### 子类型关系

```rust
// 'static 是 'a 的子类型
// 因为 'static 比任何 'a 都长

let s: &'static str = "hello";
take_str(s);  // 可以传给需要 &'a str 的函数

fn take_str<'a>(s: &'a str) {}
```

---

## 第四部分：结构体中的生命周期

```rust
struct Person<'a> {
    name: &'a str,  // name必须活得比Person长
}

fn main() {
    let name = String::from("Alice");
    let p = Person { name: &name };
    // name必须在这里之后才能drop
    println!("{}", p.name);
}
```

---

## 第五部分：常见模式

### 模式1: 输入输出相同

```rust
fn identity<'a>(x: &'a str) -> &'a str {
    x
}
```

### 模式2: 多个独立生命周期

```rust
fn parse<'a, 'b>(
    input: &'a str,
    config: &'b Config
) -> &'a str {
    // 返回与input关联的数据
}
```

### 模式3: 方法

```rust
impl<'a> Person<'a> {
    fn get_name(&self) -> &'a str {
        self.name
    }
}
```

---

## 第六部分：高级话题

### NLL (非词法生命周期)

```rust
let mut x = 5;
let y = &x;
println!("{}", y);  // y最后一次使用
// 这里y已经结束
let z = &mut x;  // OK！NLL允许
```

### HRTB (高阶trait bound)

```rust
fn call_with_ref<F>(f: F)
where
    F: for<'a> Fn(&'a str),
{
    f("hello");
}
```

---

## 总结

```
生命周期
    │
    ├──→ 核心思想
    │       └── 引用不能比数据活得长
    │
    ├──→ 语法
    │       ├── 显式标注: 'a
    │       ├── 省略规则
    │       └── 'static
    │
    └──→ 应用
            ├── 函数
            ├── 结构体
            └── trait
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 教程：理解生命周期 (3/5教程)
