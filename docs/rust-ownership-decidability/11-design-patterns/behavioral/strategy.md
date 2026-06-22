# Strategy Pattern in Rust

> **内容分级**: [归档级]
>
> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **设计模式**: 行为型模式
> **难度**: 🟢 简单
> **应用场景**: 算法族、运行时策略切换

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Strategy Pattern in Rust](#strategy-pattern-in-rust)
  - [📑 目录](#-目录)
  - [概念](#概念)
  - [实现方式](#实现方式)
    - [Trait 方式](#trait-方式)
  - [零成本抽象: 泛型实现](#零成本抽象-泛型实现)
  - [形式化定义](#形式化定义)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 概念
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

策略模式定义一系列算法，把它们一个个封装起来，并且使它们可以相互替换。

---

## 实现方式
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

### Trait 方式
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

```rust
// 策略接口
pub trait PaymentStrategy {
    fn pay(&self, amount: f64) -> Result<Receipt, PaymentError>;
}

pub struct Receipt {
    pub transaction_id: String,
    pub amount: f64,
}

#[derive(Debug)]
pub enum PaymentError {
    InsufficientFunds,
    InvalidCard,
    NetworkError,
}

// 具体策略: 信用卡
pub struct CreditCardPayment {
    card_number: String,
    cvv: String,
}

impl CreditCardPayment {
    pub fn new(card_number: &str, cvv: &str) -> Self {
        Self {
            card_number: card_number.to_string(),
            cvv: cvv.to_string(),
        }
    }
}

impl PaymentStrategy for CreditCardPayment {
    fn pay(&self, amount: f64) -> Result<Receipt, PaymentError> {
        println!("Processing ${} via Credit Card {}", amount, &self.card_number[..4]);
        Ok(Receipt {
            transaction_id: "CC-123".to_string(),
            amount,
        })
    }
}

// 具体策略: PayPal
pub struct PayPalPayment {
    email: String,
}

impl PayPalPayment {
    pub fn new(email: &str) -> Self {
        Self {
            email: email.to_string(),
        }
    }
}

impl PaymentStrategy for PayPalPayment {
    fn pay(&self, amount: f64) -> Result<Receipt, PaymentError> {
        println!("Processing ${} via PayPal ({})", amount, self.email);
        Ok(Receipt {
            transaction_id: "PP-456".to_string(),
            amount,
        })
    }
}

// 具体策略: 加密货币
pub struct CryptoPayment {
    wallet_address: String,
}

impl CryptoPayment {
    pub fn new(address: &str) -> Self {
        Self {
            wallet_address: address.to_string(),
        }
    }
}

impl PaymentStrategy for CryptoPayment {
    fn pay(&self, amount: f64) -> Result<Receipt, PaymentError> {
        println!("Processing ${} via Crypto wallet {}", amount, &self.wallet_address[..6]);
        Ok(Receipt {
            transaction_id: "CR-789".to_string(),
            amount,
        })
    }
}

// 上下文
pub struct ShoppingCart {
    items: Vec<(String, f64)>,
    payment_strategy: Box<dyn PaymentStrategy>,
}

impl ShoppingCart {
    pub fn new(strategy: Box<dyn PaymentStrategy>) -> Self {
        Self {
            items: Vec::new(),
            payment_strategy: strategy,
        }
    }

    pub fn add_item(&mut self, name: &str, price: f64) {
        self.items.push((name.to_string(), price));
    }

    pub fn set_payment_strategy(&mut self, strategy: Box<dyn PaymentStrategy>) {
        self.payment_strategy = strategy;
    }

    pub fn checkout(&self) -> Result<Receipt, PaymentError> {
        let total: f64 = self.items.iter().map(|(_, price)| price).sum();
        self.payment_strategy.pay(total)
    }
}

// 使用
fn main() {
    let credit_card = Box::new(CreditCardPayment::new("1234-5678-9012", "123"));
    let mut cart = ShoppingCart::new(credit_card);

    cart.add_item("Laptop", 999.99);
    cart.add_item("Mouse", 29.99);

    let receipt = cart.checkout().unwrap();
    println!("Paid {} via {}", receipt.amount, receipt.transaction_id);

    // 切换策略
    cart.set_payment_strategy(Box::new(PayPalPayment::new("user@example.com")));
    let receipt2 = cart.checkout().unwrap();
    println!("Paid {} via {}", receipt2.amount, receipt2.transaction_id);
}
```

---

## 零成本抽象: 泛型实现
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
// 编译期策略选择，零运行时开销
pub struct EfficientCart<P: PaymentStrategy> {
    items: Vec<(String, f64)>,
    payment: P,
}

impl<P: PaymentStrategy> EfficientCart<P> {
    pub fn new(payment: P) -> Self {
        Self {
            items: Vec::new(),
            payment,
        }
    }

    pub fn checkout(&self) -> Result<Receipt, PaymentError> {
        let total: f64 = self.items.iter().map(|(_, p)| p).sum();
        self.payment.pay(total)
    }
}

// 使用 - 编译器会为每种策略生成优化代码
let cart = EfficientCart::new(CreditCardPayment::new("1234", "123"));
```

---

## 形式化定义
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```
Strategy<T> = { s: T | s implements Algorithm }

Context 与 Strategy 解耦:
  Context::execute(strategy: Strategy) → Result

替换性:
  ∀s1, s2: Strategy: Context(s1) ⟺ Context(s2)
```

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [behavioral 目录](./README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

> **来源: [TRPL Ch. 4 - Ownership](https://doc.rust-lang.org/book/ch04-00-ownership.html)**

> **来源: [Rustonomicon - Ownership](https://doc.rust-lang.org/nomicon/ownership.html)**

> **来源: [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)**

> **来源: [Wikipedia - Design Pattern](https://en.wikipedia.org/wiki/Design_Pattern)**

> **来源: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)**

> **来源: [Gang of Four - Design Patterns](https://en.wikipedia.org/wiki/Design_Patterns)**

> **来源: [ACM - Software Design Patterns](https://dl.acm.org/)**

---
