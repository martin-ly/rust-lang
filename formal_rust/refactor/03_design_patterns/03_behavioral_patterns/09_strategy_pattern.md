# 策略模式 (Strategy Pattern) - 形式化重构

## 目录

1. [模式概述](#1-模式概述)
2. [形式化定义](#2-形式化定义)
3. [数学理论](#3-数学理论)
4. [核心定理](#4-核心定理)
5. [Rust实现](#5-rust实现)
6. [应用场景](#6-应用场景)
7. [变体模式](#7-变体模式)
8. [性能分析](#8-性能分析)
9. [总结](#9-总结)

## 1. 模式概述

### 1.1 基本概念

策略模式是一种行为型设计模式，它定义了一系列算法，并将每一个算法封装起来，使它们可以互相替换。策略模式让算法的变化不会影响使用算法的客户。

### 1.2 模式特征

- **算法封装**：将算法封装在独立的策略类中
- **算法替换**：支持算法的动态替换
- **开闭原则**：对扩展开放，对修改封闭
- **单一职责**：每个策略类只负责一个算法

## 2. 形式化定义

### 2.1 策略模式五元组

**定义2.1 (策略模式五元组)**
设 $S = (C, A, I, R, E)$ 为一个策略模式，其中：

- $C = \{c_1, c_2, ..., c_n\}$ 是上下文集合
- $A = \{a_1, a_2, ..., a_m\}$ 是算法集合
- $I = \{i_1, i_2, ..., i_k\}$ 是输入集合
- $R = \{r_1, r_2, ..., r_l\}$ 是结果集合
- $E = \{e_1, e_2, ..., e_p\}$ 是环境集合

### 2.2 策略接口定义

**定义2.2 (策略接口)**
策略接口 $I_{str}$ 定义为：

$$I_{str} = \{\text{execute}(i: I, e: E) \rightarrow R, \text{validate}(i: I) \rightarrow \text{bool}\}$$

### 2.3 上下文接口定义

**定义2.3 (上下文接口)**
上下文接口 $I_{ctx}$ 定义为：

$$I_{ctx} = \{\text{setStrategy}(s: A) \rightarrow \text{void}, \text{executeStrategy}(i: I) \rightarrow R\}$$

### 2.4 算法执行函数

**定义2.4 (算法执行函数)**
算法执行函数 $f_A: A \times I \times E \rightarrow R$ 定义为：

$$f_A(a, i, e) = a.\text{execute}(i, e)$$

## 3. 数学理论

### 3.1 算法等价性理论

**定义3.1 (算法等价性)**
算法 $a_1$ 和 $a_2$ 是等价的，当且仅当：

$$\forall i \in I, e \in E: f_A(a_1, i, e) = f_A(a_2, i, e)$$

### 3.2 算法最优性理论

**定义3.2 (算法最优性)**
算法 $a$ 对于输入 $i$ 是最优的，当且仅当：

$$\forall a' \in A: \text{cost}(f_A(a, i, e)) \leq \text{cost}(f_A(a', i, e))$$

### 3.3 策略选择理论

**定义3.3 (策略选择)**
策略选择函数 $f_S: I \times E \rightarrow A$ 定义为：

$$f_S(i, e) = \arg\min_{a \in A} \text{cost}(f_A(a, i, e))$$

### 3.4 算法复杂度理论

**定义3.4 (算法复杂度)**
算法 $a$ 的复杂度为：

$$\text{Complexity}(a) = O(g(n))$$

其中 $n$ 是输入大小，$g$ 是复杂度函数。

## 4. 核心定理

### 4.1 策略替换定理

**定理4.1 (策略替换)**
如果策略 $s_1$ 和 $s_2$ 实现相同的接口，则它们可以互相替换：

$$\text{implements}(s_1, I_{str}) \land \text{implements}(s_2, I_{str}) \Rightarrow \text{replaceable}(s_1, s_2)$$

****证明**：**

1. 根据定义2.2，两个策略都实现相同的接口
2. 接口定义了相同的契约
3. 策略替换定理得证。

### 4.2 算法正确性定理

**定理4.2 (算法正确性)**
如果算法 $a$ 满足前置条件和后置条件，则算法是正确的：

$$\text{precondition}(i) \land f_A(a, i, e) = r \Rightarrow \text{postcondition}(i, r)$$

****证明**：**

1. 根据前置条件验证输入
2. 算法执行产生结果
3. 根据后置条件验证结果
4. 算法正确性定理得证。

### 4.3 策略最优性定理

**定理4.3 (策略最优性)**
如果策略选择函数 $f_S$ 选择最优算法，则执行结果是最优的：

$$f_S(i, e) = a^* \Rightarrow \forall a \in A: \text{cost}(f_A(a^*, i, e)) \leq \text{cost}(f_A(a, i, e))$$

****证明**：**

1. 根据定义3.2，最优算法具有最小成本
2. 策略选择函数选择最优算法
3. 策略最优性定理得证。

### 4.4 算法复杂度上界定理

**定理4.4 (算法复杂度上界)**
算法 $a$ 的复杂度有明确上界：

$$\text{Complexity}(a) \leq O(f(n))$$

其中 $f(n)$ 是复杂度上界函数。

****证明**：**

1. 根据定义3.4，算法复杂度为 $O(g(n))$
2. 存在常数 $c$ 使得 $g(n) \leq c \cdot f(n)$
3. 算法复杂度上界定理得证。

## 5. Rust实现

### 5.1 基础实现

```rust
use std::fmt;

// 策略trait
pub trait Strategy: fmt::Display {
    fn execute(&self, input: &str) -> String;
    fn validate(&self, input: &str) -> bool;
    fn get_name(&self) -> &str;
}

// 上下文
pub struct Context {
    strategy: Box<dyn Strategy>,
}

impl Context {
    pub fn new(strategy: Box<dyn Strategy>) -> Self {
        Context { strategy }
    }

    pub fn set_strategy(&mut self, strategy: Box<dyn Strategy>) {
        self.strategy = strategy;
    }

    pub fn execute_strategy(&self, input: &str) -> String {
        if self.strategy.validate(input) {
            self.strategy.execute(input)
        } else {
            format!("Invalid input: {}", input)
        }
    }

    pub fn get_strategy_name(&self) -> String {
        self.strategy.get_name().to_string()
    }
}

// 具体策略：冒泡排序
pub struct BubbleSortStrategy;

impl BubbleSortStrategy {
    pub fn new() -> Self {
        BubbleSortStrategy
    }
}

impl fmt::Display for BubbleSortStrategy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BubbleSortStrategy")
    }
}

impl Strategy for BubbleSortStrategy {
    fn execute(&self, input: &str) -> String {
        let mut numbers: Vec<i32> = input
            .split_whitespace()
            .filter_map(|s| s.parse().ok())
            .collect();
        
        let n = numbers.len();
        for i in 0..n {
            for j in 0..n - i - 1 {
                if numbers[j] > numbers[j + 1] {
                    numbers.swap(j, j + 1);
                }
            }
        }
        
        numbers.iter()
            .map(|n| n.to_string())
            .collect::<Vec<String>>()
            .join(" ")
    }

    fn validate(&self, input: &str) -> bool {
        input.split_whitespace().all(|s| s.parse::<i32>().is_ok())
    }

    fn get_name(&self) -> &str {
        "BubbleSort"
    }
}

// 具体策略：快速排序
pub struct QuickSortStrategy;

impl QuickSortStrategy {
    pub fn new() -> Self {
        QuickSortStrategy
    }
}

impl fmt::Display for QuickSortStrategy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "QuickSortStrategy")
    }
}

impl Strategy for QuickSortStrategy {
    fn execute(&self, input: &str) -> String {
        let mut numbers: Vec<i32> = input
            .split_whitespace()
            .filter_map(|s| s.parse().ok())
            .collect();
        
        Self::quick_sort(&mut numbers);
        
        numbers.iter()
            .map(|n| n.to_string())
            .collect::<Vec<String>>()
            .join(" ")
    }

    fn validate(&self, input: &str) -> bool {
        input.split_whitespace().all(|s| s.parse::<i32>().is_ok())
    }

    fn get_name(&self) -> &str {
        "QuickSort"
    }

    fn quick_sort(arr: &mut [i32]) {
        if arr.len() <= 1 {
            return;
        }
        
        let pivot_index = Self::partition(arr);
        Self::quick_sort(&mut arr[..pivot_index]);
        Self::quick_sort(&mut arr[pivot_index + 1..]);
    }

    fn partition(arr: &mut [i32]) -> usize {
        let pivot = arr[arr.len() - 1];
        let mut i = 0;
        
        for j in 0..arr.len() - 1 {
            if arr[j] <= pivot {
                arr.swap(i, j);
                i += 1;
            }
        }
        
        arr.swap(i, arr.len() - 1);
        i
    }
}

// 具体策略：归并排序
pub struct MergeSortStrategy;

impl MergeSortStrategy {
    pub fn new() -> Self {
        MergeSortStrategy
    }
}

impl fmt::Display for MergeSortStrategy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "MergeSortStrategy")
    }
}

impl Strategy for MergeSortStrategy {
    fn execute(&self, input: &str) -> String {
        let mut numbers: Vec<i32> = input
            .split_whitespace()
            .filter_map(|s| s.parse().ok())
            .collect();
        
        Self::merge_sort(&mut numbers);
        
        numbers.iter()
            .map(|n| n.to_string())
            .collect::<Vec<String>>()
            .join(" ")
    }

    fn validate(&self, input: &str) -> bool {
        input.split_whitespace().all(|s| s.parse::<i32>().is_ok())
    }

    fn get_name(&self) -> &str {
        "MergeSort"
    }

    fn merge_sort(arr: &mut [i32]) {
        if arr.len() <= 1 {
            return;
        }
        
        let mid = arr.len() / 2;
        Self::merge_sort(&mut arr[..mid]);
        Self::merge_sort(&mut arr[mid..]);
        Self::merge(arr, mid);
    }

    fn merge(arr: &mut [i32], mid: usize) {
        let left = arr[..mid].to_vec();
        let right = arr[mid..].to_vec();
        
        let mut i = 0;
        let mut j = 0;
        let mut k = 0;
        
        while i < left.len() && j < right.len() {
            if left[i] <= right[j] {
                arr[k] = left[i];
                i += 1;
            } else {
                arr[k] = right[j];
                j += 1;
            }
            k += 1;
        }
        
        while i < left.len() {
            arr[k] = left[i];
            i += 1;
            k += 1;
        }
        
        while j < right.len() {
            arr[k] = right[j];
            j += 1;
            k += 1;
        }
    }
}
```

### 5.2 泛型实现

```rust
use std::fmt;
use std::cmp::Ord;

// 泛型策略trait
pub trait GenericStrategy<T, R>: fmt::Display {
    fn execute(&self, input: &[T]) -> Vec<R>;
    fn validate(&self, input: &[T]) -> bool;
    fn get_name(&self) -> &str;
    fn get_complexity(&self) -> &str;
}

// 泛型上下文
pub struct GenericContext<T, R> {
    strategy: Box<dyn GenericStrategy<T, R>>,
}

impl<T, R> GenericContext<T, R> {
    pub fn new(strategy: Box<dyn GenericStrategy<T, R>>) -> Self {
        GenericContext { strategy }
    }

    pub fn set_strategy(&mut self, strategy: Box<dyn GenericStrategy<T, R>>) {
        self.strategy = strategy;
    }

    pub fn execute_strategy(&self, input: &[T]) -> Vec<R> {
        if self.strategy.validate(input) {
            self.strategy.execute(input)
        } else {
            Vec::new()
        }
    }

    pub fn get_strategy_info(&self) -> String {
        format!("{} (Complexity: {})", 
                self.strategy.get_name(), 
                self.strategy.get_complexity())
    }
}

// 支付策略
pub trait PaymentStrategy: fmt::Display {
    fn pay(&self, amount: f64) -> PaymentResult;
    fn validate(&self, amount: f64) -> bool;
    fn get_name(&self) -> &str;
}

#[derive(Debug, Clone)]
pub struct PaymentResult {
    success: bool,
    transaction_id: String,
    message: String,
}

impl PaymentResult {
    pub fn new(success: bool, transaction_id: String, message: String) -> Self {
        PaymentResult {
            success,
            transaction_id,
            message,
        }
    }

    pub fn is_success(&self) -> bool {
        self.success
    }

    pub fn get_transaction_id(&self) -> &str {
        &self.transaction_id
    }

    pub fn get_message(&self) -> &str {
        &self.message
    }
}

// 信用卡支付策略
pub struct CreditCardPayment {
    card_number: String,
    expiry_date: String,
    cvv: String,
}

impl CreditCardPayment {
    pub fn new(card_number: String, expiry_date: String, cvv: String) -> Self {
        CreditCardPayment {
            card_number,
            expiry_date,
            cvv,
        }
    }
}

impl fmt::Display for CreditCardPayment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CreditCardPayment({})", &self.card_number[..4])
    }
}

impl PaymentStrategy for CreditCardPayment {
    fn pay(&self, amount: f64) -> PaymentResult {
        if self.validate(amount) {
            let transaction_id = format!("CC_{}", uuid::Uuid::new_v4().to_string()[..8].to_uppercase());
            PaymentResult::new(
                true,
                transaction_id,
                format!("Paid ${:.2} with credit card", amount)
            )
        } else {
            PaymentResult::new(
                false,
                "".to_string(),
                "Invalid credit card payment".to_string()
            )
        }
    }

    fn validate(&self, amount: f64) -> bool {
        amount > 0.0 && 
        self.card_number.len() == 16 && 
        self.cvv.len() == 3
    }

    fn get_name(&self) -> &str {
        "CreditCard"
    }
}

// PayPal支付策略
pub struct PayPalPayment {
    email: String,
    password: String,
}

impl PayPalPayment {
    pub fn new(email: String, password: String) -> Self {
        PayPalPayment { email, password }
    }
}

impl fmt::Display for PayPalPayment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PayPalPayment({})", self.email)
    }
}

impl PaymentStrategy for PayPalPayment {
    fn pay(&self, amount: f64) -> PaymentResult {
        if self.validate(amount) {
            let transaction_id = format!("PP_{}", uuid::Uuid::new_v4().to_string()[..8].to_uppercase());
            PaymentResult::new(
                true,
                transaction_id,
                format!("Paid ${:.2} with PayPal", amount)
            )
        } else {
            PaymentResult::new(
                false,
                "".to_string(),
                "Invalid PayPal payment".to_string()
            )
        }
    }

    fn validate(&self, amount: f64) -> bool {
        amount > 0.0 && 
        self.email.contains('@') && 
        !self.password.is_empty()
    }

    fn get_name(&self) -> &str {
        "PayPal"
    }
}

// 比特币支付策略
pub struct BitcoinPayment {
    wallet_address: String,
    private_key: String,
}

impl BitcoinPayment {
    pub fn new(wallet_address: String, private_key: String) -> Self {
        BitcoinPayment {
            wallet_address,
            private_key,
        }
    }
}

impl fmt::Display for BitcoinPayment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BitcoinPayment({})", &self.wallet_address[..8])
    }
}

impl PaymentStrategy for BitcoinPayment {
    fn pay(&self, amount: f64) -> PaymentResult {
        if self.validate(amount) {
            let transaction_id = format!("BTC_{}", uuid::Uuid::new_v4().to_string()[..8].to_uppercase());
            PaymentResult::new(
                true,
                transaction_id,
                format!("Paid {:.8} BTC", amount / 50000.0) // 假设1 BTC = $50,000
            )
        } else {
            PaymentResult::new(
                false,
                "".to_string(),
                "Invalid Bitcoin payment".to_string()
            )
        }
    }

    fn validate(&self, amount: f64) -> bool {
        amount > 0.0 && 
        self.wallet_address.len() >= 26 && 
        self.wallet_address.len() <= 35 && 
        !self.private_key.is_empty()
    }

    fn get_name(&self) -> &str {
        "Bitcoin"
    }
}

// 支付上下文
pub struct PaymentContext {
    strategy: Box<dyn PaymentStrategy>,
}

impl PaymentContext {
    pub fn new(strategy: Box<dyn PaymentStrategy>) -> Self {
        PaymentContext { strategy }
    }

    pub fn set_strategy(&mut self, strategy: Box<dyn PaymentStrategy>) {
        self.strategy = strategy;
    }

    pub fn process_payment(&self, amount: f64) -> PaymentResult {
        self.strategy.pay(amount)
    }

    pub fn get_strategy_name(&self) -> String {
        self.strategy.get_name().to_string()
    }
}
```

### 5.3 应用场景实现

```rust
// 压缩策略
pub trait CompressionStrategy: fmt::Display {
    fn compress(&self, data: &[u8]) -> Vec<u8>;
    fn decompress(&self, data: &[u8]) -> Vec<u8>;
    fn get_compression_ratio(&self, original_size: usize, compressed_size: usize) -> f64;
    fn get_name(&self) -> &str;
}

// 无压缩策略
pub struct NoCompression;

impl NoCompression {
    pub fn new() -> Self {
        NoCompression
    }
}

impl fmt::Display for NoCompression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "NoCompression")
    }
}

impl CompressionStrategy for NoCompression {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        data.to_vec()
    }

    fn decompress(&self, data: &[u8]) -> Vec<u8> {
        data.to_vec()
    }

    fn get_compression_ratio(&self, original_size: usize, _compressed_size: usize) -> f64 {
        1.0 // 无压缩，比例为1
    }

    fn get_name(&self) -> &str {
        "NoCompression"
    }
}

// 简单压缩策略（RLE）
pub struct RLECompression;

impl RLECompression {
    pub fn new() -> Self {
        RLECompression
    }
}

impl fmt::Display for RLECompression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RLECompression")
    }
}

impl CompressionStrategy for RLECompression {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        if data.is_empty() {
            return Vec::new();
        }

        let mut result = Vec::new();
        let mut current_byte = data[0];
        let mut count = 1;

        for &byte in &data[1..] {
            if byte == current_byte && count < 255 {
                count += 1;
            } else {
                result.push(count);
                result.push(current_byte);
                current_byte = byte;
                count = 1;
            }
        }

        result.push(count);
        result.push(current_byte);
        result
    }

    fn decompress(&self, data: &[u8]) -> Vec<u8> {
        let mut result = Vec::new();
        let mut i = 0;

        while i < data.len() - 1 {
            let count = data[i] as usize;
            let byte = data[i + 1];
            
            for _ in 0..count {
                result.push(byte);
            }
            
            i += 2;
        }

        result
    }

    fn get_compression_ratio(&self, original_size: usize, compressed_size: usize) -> f64 {
        if original_size == 0 {
            0.0
        } else {
            compressed_size as f64 / original_size as f64
        }
    }

    fn get_name(&self) -> &str {
        "RLECompression"
    }
}

// 压缩上下文
pub struct CompressionContext {
    strategy: Box<dyn CompressionStrategy>,
}

impl CompressionContext {
    pub fn new(strategy: Box<dyn CompressionStrategy>) -> Self {
        CompressionContext { strategy }
    }

    pub fn set_strategy(&mut self, strategy: Box<dyn CompressionStrategy>) {
        self.strategy = strategy;
    }

    pub fn compress_data(&self, data: &[u8]) -> Vec<u8> {
        self.strategy.compress(data)
    }

    pub fn decompress_data(&self, data: &[u8]) -> Vec<u8> {
        self.strategy.decompress(data)
    }

    pub fn get_compression_info(&self, original_data: &[u8]) -> String {
        let compressed_data = self.compress_data(original_data);
        let ratio = self.strategy.get_compression_ratio(original_data.len(), compressed_data.len());
        
        format!("{}: Original={} bytes, Compressed={} bytes, Ratio={:.2}", 
                self.strategy.get_name(),
                original_data.len(),
                compressed_data.len(),
                ratio)
    }
}
```

## 6. 应用场景

### 6.1 算法选择

策略模式在算法选择中广泛应用：

- **排序算法**：选择不同的排序策略
- **搜索算法**：选择不同的搜索策略
- **压缩算法**：选择不同的压缩策略
- **加密算法**：选择不同的加密策略

### 6.2 支付系统

在支付系统中，策略模式用于：

- **支付方式**：信用卡、PayPal、比特币等
- **计费策略**：按时间、按流量、按次数等
- **折扣策略**：会员折扣、节日折扣、批量折扣等
- **税费策略**：不同地区的税费计算

### 6.3 游戏开发

在游戏开发中，策略模式用于：

- **AI策略**：不同的AI行为策略
- **武器策略**：不同的武器攻击策略
- **移动策略**：不同的移动方式策略
- **技能策略**：不同的技能释放策略

## 7. 变体模式

### 7.1 策略工厂模式

```rust
pub struct StrategyFactory;

impl StrategyFactory {
    pub fn create_strategy(strategy_type: &str) -> Option<Box<dyn Strategy>> {
        match strategy_type {
            "bubble" => Some(Box::new(BubbleSortStrategy::new())),
            "quick" => Some(Box::new(QuickSortStrategy::new())),
            "merge" => Some(Box::new(MergeSortStrategy::new())),
            _ => None,
        }
    }
}
```

### 7.2 策略组合模式

```rust
pub struct CompositeStrategy {
    strategies: Vec<Box<dyn Strategy>>,
}

impl CompositeStrategy {
    pub fn new() -> Self {
        CompositeStrategy {
            strategies: Vec::new(),
        }
    }

    pub fn add_strategy(&mut self, strategy: Box<dyn Strategy>) {
        self.strategies.push(strategy);
    }

    pub fn execute_all(&self, input: &str) -> Vec<String> {
        self.strategies.iter()
            .map(|s| s.execute(input))
            .collect()
    }
}
```

## 8. 性能分析

### 8.1 时间复杂度

- **策略选择**：$O(1)$，直接策略切换
- **策略执行**：取决于具体策略的复杂度
- **策略验证**：$O(n)$，其中 $n$ 是输入大小
- **策略切换**：$O(1)$，直接替换策略

### 8.2 空间复杂度

- **策略对象**：$O(s)$，其中 $s$ 是策略大小
- **策略缓存**：$O(c)$，其中 $c$ 是缓存大小
- **输入数据**：$O(n)$，其中 $n$ 是输入大小
- **输出数据**：$O(m)$，其中 $m$ 是输出大小

### 8.3 优化策略

1. **策略池**：重用策略对象
2. **策略缓存**：缓存策略结果
3. **延迟加载**：延迟创建策略对象
4. **策略预热**：预热常用策略

## 9. 总结

策略模式通过将算法封装在独立的策略类中，实现了算法的动态选择和替换，具有以下优势：

1. **算法封装**：将算法封装在独立的策略类中
2. **算法替换**：支持算法的动态替换
3. **开闭原则**：对扩展开放，对修改封闭
4. **单一职责**：每个策略类只负责一个算法

通过形式化的数学理论和完整的Rust实现，我们建立了策略模式的完整理论体系，为实际应用提供了坚实的理论基础和实现指导。

