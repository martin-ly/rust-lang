# 所有权系统理论

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> 内容已整合至： [ownership_model.md](../../../research_notes/formal_methods/ownership_model.md)

[返回理论基础](../README.md) | [返回主索引](../../00_master_index.md)

---

## 所有权的核心规则

```rust
// 规则 1：每个值都有一个所有者
fn rule1() {
    let s = String::from("hello");  // s 是所有者
    // String 数据存储在堆上，s 负责管理它
}
// s 离开作用域，内存自动释放

// 规则 2：同一时间只能有一个所有者
fn rule2() {
    let s1 = String::from("hello");
    let s2 = s1;  // 所有权从 s1 转移到 s2
    // println!("{}", s1);  // 错误：s1 不再拥有该值
    println!("{}", s2);   // OK
}

// 规则 3：当所有者离开作用域，值被丢弃
fn rule3() {
    {
        let s = String::from("hello");
        // s 在这里有效
    }  // s 离开作用域，drop(s) 被自动调用
    // s 不再有效
}
```

## 所有权与函数

```rust
fn take_ownership(s: String) {
    // s 获得所有权
    println!("{}", s);
}  // s 在这里被丢弃

fn give_ownership() -> String {
    String::from("hello")  // 所有权返回给调用者
}

fn borrow(s: &String) {
    // s 借用，不获得所有权
    println!("{}", s);
}  // s 只是借用，不会被丢弃

fn demo() {
    let s1 = String::from("hello");
    take_ownership(s1);
    // s1 在这里不再有效

    let s2 = give_ownership();
    // s2 获得所有权

    borrow(&s2);
    // s2 仍然有效，因为只是借用
}
```

## 相关研究笔记

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 所有权模型 | 所有权系统的完整形式化模型 | [../../../research_notes/formal_methods/ownership_model.md](../../../research_notes/formal_methods/ownership_model.md) |
| 借用检查器 | 借用检查的形式化证明 | [../../../research_notes/formal_methods/borrow_checker_proof.md](../../../research_notes/formal_methods/borrow_checker_proof.md) |
