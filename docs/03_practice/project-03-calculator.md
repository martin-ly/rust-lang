# 实践项目 03: 表达式计算器

> **难度**: ⭐ 入门级
> **所需知识**: c01-c04
> **预计时间**: 3-4小时

---

## 项目目标

创建一个支持四则运算和括号的表达式计算器。

---

## 功能需求

- [ ] 解析数学表达式: `calc "2 + 3 * 4"`
- [ ] 支持 +, -, *, / 运算符
- [ ] 支持括号: `(2 + 3) * 4`
- [ ] 错误处理: 除零、非法表达式

---

## 学习要点

### 递归下降解析

```rust
enum Expr {
    Number(f64),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
}

fn eval(expr: &Expr) -> f64 {
    match expr {
        Expr::Number(n) => *n,
        Expr::Add(a, b) => eval(a) + eval(b),
        Expr::Mul(a, b) => eval(a) * eval(b),
    }
}
```

---

## 参考实现

完整参考实现位于: `examples/calculator/`
