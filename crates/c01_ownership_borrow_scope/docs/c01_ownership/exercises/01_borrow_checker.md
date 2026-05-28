# C01 所有权练习 - 借用检查器

## 练习 1: 修复借用错误

```rust
fn main() {
    let s = String::from("hello");
    let r1 = &s;
    let r2 = &mut s; // 错误！不能同时拥有不可变和可变借用
    println!("{} {}", r1, r2);
}
```

**任务**: 修复上述代码，使其能够编译通过。

<details>
<summary>答案</summary>

```rust
fn main() {
    let mut s = String::from("hello");
    {
        let r1 = &s;
        println!("{}", r1);
    } // r1 在这里离开作用域
    let r2 = &mut s; // 现在可以创建可变借用
    println!("{}", r2);
}
```

</details>

## 练习 2: 生命周期标注

```rust
fn longest(x: &str, y: &str) -> &str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

**任务**: 为上述函数添加适当的生命周期标注。

<details>
<summary>答案</summary>

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

</details>

## 练习 3: 智能指针选择

为以下场景选择最合适的智能指针：

1. 需要在多个所有者之间共享数据，且需要修改
2. 需要保证同一时刻只有一个可变引用
3. 需要延迟初始化的全局配置

<details>
<summary>答案</summary>

1. `Arc<Mutex<T>>` - 线程安全的共享可变访问
2. `RefCell<T>` - 运行时借用检查（单线程）
3. `LazyLock<T>` 或 `OnceLock<T>` - 线程安全的延迟初始化

</details>

---

**难度**: 中级
**预计时间**: 30-45 分钟
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
