# Strategy Pattern in Rust

> **设计模式**: 行为型模式
> **难度**: 🟢 简单
> **应用场景**: 算法族、运行时策略切换

---

## 概念

策略模式定义一系列算法，把它们一个个封装起来，并且使它们可以相互替换。

---

## 实现方式

### Trait 方式

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

```rust
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

```
Strategy<T> = { s: T | s implements Algorithm }

Context 与 Strategy 解耦:
  Context::execute(strategy: Strategy) → Result

替换性:
  ∀s1, s2: Strategy: Context(s1) ⟺ Context(s2)
```
