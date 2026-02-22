# 宏速查卡

> **一页纸速查** - 声明宏、过程宏、常用宏

---

## 声明宏 (macro_rules!)

```rust
macro_rules! say_hello {
    () => {
        println!("Hello!");
    };
    ($name:expr) => {
        println!("Hello, {}!", $name);
    };
}

// 使用
say_hello!();          // Hello!
say_hello!("World");   // Hello, World!
```

---

## 常用宏

| 宏 | 用途 | 示例 |
|:---|:---|:---|
| `println!` | 打印 | `println!("{}", x)` |
| `format!` | 格式化字符串 | `format!("{}", x)` |
| `vec!` | 创建Vec | `vec![1, 2, 3]` |
| `assert!` | 断言 | `assert!(x > 0)` |
| `panic!` | panic | `panic!("error")` |
| `todo!` | 待实现 | `todo!("implement")` |
| `unreachable!` | 不可达 | `unreachable!()` |

---

## 派生宏

```rust
#[derive(Debug, Clone, PartialEq)]
struct Point { x: i32, y: i32 }
```

常用trait: `Debug`, `Clone`, `Copy`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash`, `Default`

---

## 属性宏

```rust
#[test]           // 测试函数
#[inline]         // 内联建议
#[cfg(test)]      // 条件编译
#[derive(...)]    // 自动实现
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 宏速查卡 (5/5速查卡全部完成！)
