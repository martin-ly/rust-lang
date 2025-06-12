# 观察者模式 (Observer Pattern) - 形式化重构

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

观察者模式是一种行为型设计模式，它定义了一种一对多的依赖关系，让多个观察者对象同时监听某一个主题对象。当主题对象发生变化时，它的所有依赖者都会得到通知并自动更新。

### 1.2 模式特征

- **一对多关系**：一个主题可以有多个观察者
- **松耦合**：主题和观察者之间松耦合
- **自动通知**：主题变化时自动通知观察者
- **动态绑定**：观察者可以动态添加和删除

## 2. 形式化定义

### 2.1 观察者模式五元组

**定义2.1 (观察者模式五元组)**
设 $O = (S, B, N, U, T)$ 为一个观察者模式，其中：

- $S = \{s_1, s_2, ..., s_n\}$ 是主题集合
- $B = \{b_1, b_2, ..., b_m\}$ 是观察者集合
- $N = \{n_1, n_2, ..., n_k\}$ 是通知类型集合
- $U = \{u_1, u_2, ..., u_l\}$ 是更新操作集合
- $T = \{t_1, t_2, ..., t_p\}$ 是时间戳集合

### 2.2 主题接口定义

**定义2.2 (主题接口)**
主题接口 $I_{sub}$ 定义为：

$$I_{sub} = \{\text{attach}(o: B) \rightarrow \text{void}, \text{detach}(o: B) \rightarrow \text{void}, \text{notify}() \rightarrow \text{void}\}$$

### 2.3 观察者接口定义

**定义2.3 (观察者接口)**
观察者接口 $I_{obs}$ 定义为：

$$I_{obs} = \{\text{update}(s: S, data: D) \rightarrow \text{void}\}$$

### 2.4 通知函数定义

**定义2.4 (通知函数)**
通知函数 $f_N: S \times B \times D \rightarrow \text{void}$ 定义为：

$$f_N(s, b, data) = b.\text{update}(s, data)$$

## 3. 数学理论

### 3.1 观察关系理论

**定义3.1 (观察关系)**
观察关系 $R_{obs} \subseteq S \times B$ 定义为：

$$R_{obs} = \{(s, b) | b \text{ observes } s\}$$

### 3.2 通知完整性理论

**定义3.2 (通知完整性)**
主题 $s$ 的通知是完整的，当且仅当：

$$\forall b \in B: (s, b) \in R_{obs} \Rightarrow b.\text{update}(s, data)$$

### 3.3 观察者一致性理论

**定义3.3 (观察者一致性)**
观察者集合 $B$ 对于主题 $s$ 是一致的，当且仅当：

$$\forall b_1, b_2 \in B: b_1.\text{getState}() = b_2.\text{getState}()$$

### 3.4 通知顺序理论

**定义3.4 (通知顺序)**
通知顺序 $O_N$ 是确定的，当且仅当：

$$\forall b_1, b_2 \in B: \text{notifyOrder}(b_1, b_2) \text{ is consistent}$$

## 4. 核心定理

### 4.1 通知完整性定理

**定理4.1 (通知完整性)**
如果主题 $s$ 执行通知操作，则所有观察者都会收到通知：

$$\text{notify}(s) \Rightarrow \forall b \in B: (s, b) \in R_{obs} \Rightarrow b.\text{update}(s, data)$$

**证明：**

1. 根据定义2.2，`notify()` 方法会通知所有观察者
2. 根据定义3.2，通知完整性保证所有观察者都被通知
3. 通知完整性定理得证。

### 4.2 观察者一致性定理

**定理4.2 (观察者一致性)**
如果所有观察者都正确更新，则观察者状态一致：

$$\forall b \in B: b.\text{update}(s, data) \Rightarrow \text{consistent}(B)$$

**证明：**

1. 根据定义3.3，所有观察者都收到相同的更新数据
2. 更新操作是确定性的
3. 观察者一致性定理得证。

### 4.3 通知传递性定理

**定理4.3 (通知传递性)**
如果观察者 $b_1$ 观察主题 $s_1$，$s_1$ 观察主题 $s_2$，则 $b_1$ 间接观察 $s_2$：

$$(b_1, s_1) \in R_{obs} \land (s_1, s_2) \in R_{obs} \Rightarrow (b_1, s_2) \in R_{obs}^*$$

**证明：**

1. 根据观察关系的传递性
2. 通知会沿着观察关系链传递
3. 通知传递性定理得证。

### 4.4 观察者数量定理

**定理4.4 (观察者数量)**
主题 $s$ 的观察者数量有上界：

$$|B_s| \leq \text{maxObservers}$$

其中 $B_s = \{b | (s, b) \in R_{obs}\}$。

**证明：**

1. 系统资源有限
2. 观察者数量受内存和性能限制
3. 观察者数量定理得证。

## 5. Rust实现

### 5.1 基础实现

```rust
use std::fmt;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// 观察者trait
pub trait Observer: fmt::Display + Send + Sync {
    fn update(&self, subject: &dyn Subject, data: &str);
    fn get_id(&self) -> &str;
}

// 主题trait
pub trait Subject: fmt::Display + Send + Sync {
    fn attach(&mut self, observer: Arc<dyn Observer>);
    fn detach(&mut self, observer_id: &str);
    fn notify(&self, data: &str);
    fn get_state(&self) -> String;
    fn set_state(&mut self, state: String);
}

// 具体主题：天气数据
pub struct WeatherData {
    observers: Vec<Arc<dyn Observer>>,
    temperature: f32,
    humidity: f32,
    pressure: f32,
}

impl WeatherData {
    pub fn new() -> Self {
        WeatherData {
            observers: Vec::new(),
            temperature: 0.0,
            humidity: 0.0,
            pressure: 0.0,
        }
    }

    pub fn set_measurements(&mut self, temperature: f32, humidity: f32, pressure: f32) {
        self.temperature = temperature;
        self.humidity = humidity;
        self.pressure = pressure;
        
        let data = format!("T:{:.1}°C, H:{:.1}%, P:{:.1}hPa", 
                          temperature, humidity, pressure);
        self.notify(&data);
    }

    pub fn get_temperature(&self) -> f32 {
        self.temperature
    }

    pub fn get_humidity(&self) -> f32 {
        self.humidity
    }

    pub fn get_pressure(&self) -> f32 {
        self.pressure
    }
}

impl fmt::Display for WeatherData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "WeatherData(T:{:.1}°C, H:{:.1}%, P:{:.1}hPa)", 
               self.temperature, self.humidity, self.pressure)
    }
}

impl Subject for WeatherData {
    fn attach(&mut self, observer: Arc<dyn Observer>) {
        self.observers.push(observer);
    }

    fn detach(&mut self, observer_id: &str) {
        self.observers.retain(|obs| obs.get_id() != observer_id);
    }

    fn notify(&self, data: &str) {
        for observer in &self.observers {
            observer.update(self, data);
        }
    }

    fn get_state(&self) -> String {
        format!("{}|{}|{}", self.temperature, self.humidity, self.pressure)
    }

    fn set_state(&mut self, state: String) {
        let parts: Vec<&str> = state.split('|').collect();
        if parts.len() >= 3 {
            self.temperature = parts[0].parse().unwrap_or(0.0);
            self.humidity = parts[1].parse().unwrap_or(0.0);
            self.pressure = parts[2].parse().unwrap_or(0.0);
        }
    }
}

// 具体观察者：当前状况显示
pub struct CurrentConditionsDisplay {
    id: String,
    temperature: f32,
    humidity: f32,
}

impl CurrentConditionsDisplay {
    pub fn new(id: String) -> Self {
        CurrentConditionsDisplay {
            id,
            temperature: 0.0,
            humidity: 0.0,
        }
    }

    pub fn display(&self) {
        println!("[{}] Current conditions: {:.1}°C and {:.1}% humidity", 
                self.id, self.temperature, self.humidity);
    }
}

impl fmt::Display for CurrentConditionsDisplay {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CurrentConditionsDisplay({}: {:.1}°C, {:.1}%)", 
               self.id, self.temperature, self.humidity)
    }
}

impl Observer for CurrentConditionsDisplay {
    fn update(&self, subject: &dyn Subject, data: &str) {
        // 解析天气数据
        let parts: Vec<&str> = data.split(',').collect();
        if parts.len() >= 2 {
            if let Some(temp_str) = parts[0].strip_prefix("T:") {
                if let Some(temp) = temp_str.strip_suffix("°C") {
                    self.temperature = temp.parse().unwrap_or(0.0);
                }
            }
            if let Some(hum_str) = parts[1].strip_prefix(" H:") {
                if let Some(hum) = hum_str.strip_suffix("%") {
                    self.humidity = hum.parse().unwrap_or(0.0);
                }
            }
        }
        
        self.display();
    }

    fn get_id(&self) -> &str {
        &self.id
    }
}

// 具体观察者：统计显示
pub struct StatisticsDisplay {
    id: String,
    max_temp: f32,
    min_temp: f32,
    temp_sum: f32,
    num_readings: u32,
}

impl StatisticsDisplay {
    pub fn new(id: String) -> Self {
        StatisticsDisplay {
            id,
            max_temp: f32::NEG_INFINITY,
            min_temp: f32::INFINITY,
            temp_sum: 0.0,
            num_readings: 0,
        }
    }

    pub fn display(&self) {
        if self.num_readings > 0 {
            let avg_temp = self.temp_sum / self.num_readings as f32;
            println!("[{}] Avg/Max/Min temperature = {:.1}°C/{:.1}°C/{:.1}°C", 
                    self.id, avg_temp, self.max_temp, self.min_temp);
        }
    }
}

impl fmt::Display for StatisticsDisplay {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StatisticsDisplay({}: avg={:.1}°C, max={:.1}°C, min={:.1}°C)", 
               self.id, 
               if self.num_readings > 0 { self.temp_sum / self.num_readings as f32 } else { 0.0 },
               self.max_temp,
               self.min_temp)
    }
}

impl Observer for StatisticsDisplay {
    fn update(&self, subject: &dyn Subject, data: &str) {
        // 解析温度数据
        let parts: Vec<&str> = data.split(',').collect();
        if let Some(temp_str) = parts[0].strip_prefix("T:") {
            if let Some(temp) = temp_str.strip_suffix("°C") {
                let temperature = temp.parse().unwrap_or(0.0);
                self.max_temp = self.max_temp.max(temperature);
                self.min_temp = self.min_temp.min(temperature);
                self.temp_sum += temperature;
                self.num_readings += 1;
            }
        }
        
        self.display();
    }

    fn get_id(&self) -> &str {
        &self.id
    }
}

// 具体观察者：预测显示
pub struct ForecastDisplay {
    id: String,
    current_pressure: f32,
    last_pressure: f32,
}

impl ForecastDisplay {
    pub fn new(id: String) -> Self {
        ForecastDisplay {
            id,
            current_pressure: 0.0,
            last_pressure: 0.0,
        }
    }

    pub fn display(&self) {
        if self.last_pressure > 0.0 {
            if self.current_pressure > self.last_pressure {
                println!("[{}] Improving weather on the way!", self.id);
            } else if self.current_pressure < self.last_pressure {
                println!("[{}] Watch out for cooler, rainy weather", self.id);
            } else {
                println!("[{}] More of the same", self.id);
            }
        }
    }
}

impl fmt::Display for ForecastDisplay {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ForecastDisplay({}: current={:.1}hPa, last={:.1}hPa)", 
               self.id, self.current_pressure, self.last_pressure)
    }
}

impl Observer for ForecastDisplay {
    fn update(&self, subject: &dyn Subject, data: &str) {
        // 解析压力数据
        let parts: Vec<&str> = data.split(',').collect();
        if let Some(press_str) = parts[2].strip_prefix(" P:") {
            if let Some(press) = press_str.strip_suffix("hPa") {
                self.last_pressure = self.current_pressure;
                self.current_pressure = press.parse().unwrap_or(0.0);
            }
        }
        
        self.display();
    }

    fn get_id(&self) -> &str {
        &self.id
    }
}
```

### 5.2 泛型实现

```rust
use std::fmt;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// 泛型观察者trait
pub trait GenericObserver<T>: fmt::Display + Send + Sync {
    fn update(&self, subject: &dyn GenericSubject<T>, data: &T);
    fn get_id(&self) -> &str;
}

// 泛型主题trait
pub trait GenericSubject<T>: fmt::Display + Send + Sync {
    fn attach(&mut self, observer: Arc<dyn GenericObserver<T>>);
    fn detach(&mut self, observer_id: &str);
    fn notify(&self, data: &T);
    fn get_state(&self) -> T;
    fn set_state(&mut self, state: T);
}

// 股票数据主题
#[derive(Debug, Clone)]
pub struct StockData {
    symbol: String,
    price: f64,
    volume: u64,
    change: f64,
}

impl StockData {
    pub fn new(symbol: String, price: f64, volume: u64, change: f64) -> Self {
        StockData {
            symbol,
            price,
            volume,
            change,
        }
    }

    pub fn get_symbol(&self) -> &str {
        &self.symbol
    }

    pub fn get_price(&self) -> f64 {
        self.price
    }

    pub fn get_volume(&self) -> u64 {
        self.volume
    }

    pub fn get_change(&self) -> f64 {
        self.change
    }
}

impl fmt::Display for StockData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StockData({}: ${:.2}, vol: {}, chg: {:.2}%)", 
               self.symbol, self.price, self.volume, self.change)
    }
}

// 股票市场主题
pub struct StockMarket {
    observers: Vec<Arc<dyn GenericObserver<StockData>>>,
    stocks: HashMap<String, StockData>,
}

impl StockMarket {
    pub fn new() -> Self {
        StockMarket {
            observers: Vec::new(),
            stocks: HashMap::new(),
        }
    }

    pub fn update_stock(&mut self, symbol: String, price: f64, volume: u64, change: f64) {
        let stock_data = StockData::new(symbol.clone(), price, volume, change);
        self.stocks.insert(symbol.clone(), stock_data.clone());
        self.notify(&stock_data);
    }

    pub fn get_stock(&self, symbol: &str) -> Option<&StockData> {
        self.stocks.get(symbol)
    }

    pub fn get_all_stocks(&self) -> Vec<&StockData> {
        self.stocks.values().collect()
    }
}

impl fmt::Display for StockMarket {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StockMarket({} stocks)", self.stocks.len())
    }
}

impl GenericSubject<StockData> for StockMarket {
    fn attach(&mut self, observer: Arc<dyn GenericObserver<StockData>>) {
        self.observers.push(observer);
    }

    fn detach(&mut self, observer_id: &str) {
        self.observers.retain(|obs| obs.get_id() != observer_id);
    }

    fn notify(&self, data: &StockData) {
        for observer in &self.observers {
            observer.update(self, data);
        }
    }

    fn get_state(&self) -> StockData {
        // 返回最新的股票数据
        if let Some(latest) = self.stocks.values().last() {
            latest.clone()
        } else {
            StockData::new("".to_string(), 0.0, 0, 0.0)
        }
    }

    fn set_state(&mut self, state: StockData) {
        self.stocks.insert(state.symbol.clone(), state);
    }
}

// 股票价格显示观察者
pub struct StockPriceDisplay {
    id: String,
    stocks: HashMap<String, f64>,
}

impl StockPriceDisplay {
    pub fn new(id: String) -> Self {
        StockPriceDisplay {
            id,
            stocks: HashMap::new(),
        }
    }

    pub fn display(&self) {
        println!("[{}] Current stock prices:", self.id);
        for (symbol, price) in &self.stocks {
            println!("  {}: ${:.2}", symbol, price);
        }
    }
}

impl fmt::Display for StockPriceDisplay {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StockPriceDisplay({}: {} stocks)", self.id, self.stocks.len())
    }
}

impl GenericObserver<StockData> for StockPriceDisplay {
    fn update(&self, subject: &dyn GenericSubject<StockData>, data: &StockData) {
        self.stocks.insert(data.symbol.clone(), data.price);
        self.display();
    }

    fn get_id(&self) -> &str {
        &self.id
    }
}

// 股票变化显示观察者
pub struct StockChangeDisplay {
    id: String,
    changes: HashMap<String, f64>,
}

impl StockChangeDisplay {
    pub fn new(id: String) -> Self {
        StockChangeDisplay {
            id,
            changes: HashMap::new(),
        }
    }

    pub fn display(&self) {
        println!("[{}] Stock price changes:", self.id);
        for (symbol, change) in &self.changes {
            let direction = if *change > 0.0 { "↗" } else if *change < 0.0 { "↘" } else { "→" };
            println!("  {}: {:.2}% {}", symbol, change, direction);
        }
    }
}

impl fmt::Display for StockChangeDisplay {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StockChangeDisplay({}: {} stocks)", self.id, self.changes.len())
    }
}

impl GenericObserver<StockData> for StockChangeDisplay {
    fn update(&self, subject: &dyn GenericSubject<StockData>, data: &StockData) {
        self.changes.insert(data.symbol.clone(), data.change);
        self.display();
    }

    fn get_id(&self) -> &str {
        &self.id
    }
}
```

### 5.3 应用场景实现

```rust
// 事件系统实现
pub struct EventSystem {
    observers: HashMap<String, Vec<Arc<dyn Observer>>>,
}

#[derive(Debug, Clone)]
pub struct Event {
    event_type: String,
    data: String,
    timestamp: u64,
}

impl EventSystem {
    pub fn new() -> Self {
        EventSystem {
            observers: HashMap::new(),
        }
    }

    pub fn subscribe(&mut self, event_type: String, observer: Arc<dyn Observer>) {
        self.observers.entry(event_type).or_insert_with(Vec::new).push(observer);
    }

    pub fn unsubscribe(&mut self, event_type: &str, observer_id: &str) {
        if let Some(observers) = self.observers.get_mut(event_type) {
            observers.retain(|obs| obs.get_id() != observer_id);
        }
    }

    pub fn publish(&self, event: &Event) {
        if let Some(observers) = self.observers.get(&event.event_type) {
            for observer in observers {
                observer.update(self, &event.data);
            }
        }
    }
}

impl fmt::Display for EventSystem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "EventSystem({} event types)", self.observers.len())
    }
}

impl Subject for EventSystem {
    fn attach(&mut self, observer: Arc<dyn Observer>) {
        // 默认订阅所有事件
        self.subscribe("all".to_string(), observer);
    }

    fn detach(&mut self, observer_id: &str) {
        for observers in self.observers.values_mut() {
            observers.retain(|obs| obs.get_id() != observer_id);
        }
    }

    fn notify(&self, data: &str) {
        // 发布到所有观察者
        for observers in self.observers.values() {
            for observer in observers {
                observer.update(self, data);
            }
        }
    }

    fn get_state(&self) -> String {
        format!("EventSystem with {} event types", self.observers.len())
    }

    fn set_state(&mut self, _state: String) {
        // 事件系统的状态设置
    }
}

// 日志观察者
pub struct LogObserver {
    id: String,
    log_file: String,
}

impl LogObserver {
    pub fn new(id: String, log_file: String) -> Self {
        LogObserver { id, log_file }
    }
}

impl fmt::Display for LogObserver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LogObserver({}: {})", self.id, self.log_file)
    }
}

impl Observer for LogObserver {
    fn update(&self, subject: &dyn Subject, data: &str) {
        println!("[{}] Logging to {}: {}", self.id, self.log_file, data);
    }

    fn get_id(&self) -> &str {
        &self.id
    }
}

// 邮件通知观察者
pub struct EmailObserver {
    id: String,
    email_address: String,
}

impl EmailObserver {
    pub fn new(id: String, email_address: String) -> Self {
        EmailObserver { id, email_address }
    }
}

impl fmt::Display for EmailObserver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "EmailObserver({}: {})", self.id, self.email_address)
    }
}

impl Observer for EmailObserver {
    fn update(&self, subject: &dyn Subject, data: &str) {
        println!("[{}] Sending email to {}: {}", self.id, self.email_address, data);
    }

    fn get_id(&self) -> &str {
        &self.id
    }
}
```

## 6. 应用场景

### 6.1 用户界面系统

观察者模式在用户界面系统中广泛应用：

- **事件处理**：处理用户交互事件
- **数据绑定**：绑定数据到UI组件
- **状态同步**：同步多个UI组件的状态
- **实时更新**：实时更新显示内容

### 6.2 消息系统

在消息系统中，观察者模式用于：

- **发布订阅**：实现发布订阅模式
- **事件驱动**：实现事件驱动架构
- **消息路由**：路由消息到不同的处理器
- **实时通知**：发送实时通知

### 6.3 监控系统

在监控系统中，观察者模式用于：

- **性能监控**：监控系统性能指标
- **告警系统**：发送系统告警
- **日志记录**：记录系统日志
- **状态报告**：生成状态报告

## 7. 变体模式

### 7.1 推拉模式

```rust
// 推模式：主题主动推送数据
pub trait PushObserver: Observer {
    fn update_with_data(&self, data: &str);
}

// 拉模式：观察者主动拉取数据
pub trait PullObserver: Observer {
    fn update(&self, subject: &dyn Subject);
}
```

### 7.2 异步观察者

```rust
use tokio::sync::mpsc;

pub struct AsyncSubject {
    observers: Vec<mpsc::Sender<String>>,
}

impl AsyncSubject {
    pub fn new() -> Self {
        AsyncSubject {
            observers: Vec::new(),
        }
    }

    pub async fn notify_async(&self, data: &str) {
        for sender in &self.observers {
            let _ = sender.send(data.to_string()).await;
        }
    }
}
```

## 8. 性能分析

### 8.1 时间复杂度

- **添加观察者**：$O(1)$，直接添加到列表
- **删除观察者**：$O(n)$，其中 $n$ 是观察者数量
- **通知观察者**：$O(n)$，其中 $n$ 是观察者数量
- **查找观察者**：$O(n)$，线性查找

### 8.2 空间复杂度

- **观察者存储**：$O(n)$，其中 $n$ 是观察者数量
- **主题状态**：$O(s)$，其中 $s$ 是状态大小
- **通知数据**：$O(d)$，其中 $d$ 是数据大小

### 8.3 优化策略

1. **观察者池**：重用观察者对象
2. **批量通知**：批量处理通知
3. **异步通知**：异步处理通知
4. **观察者缓存**：缓存观察者引用

## 9. 总结

观察者模式通过定义一对多的依赖关系，实现了松耦合的事件通知机制，具有以下优势：

1. **松耦合**：主题和观察者之间松耦合
2. **可扩展性**：易于添加新的观察者
3. **动态绑定**：观察者可以动态添加和删除
4. **自动通知**：主题变化时自动通知观察者

通过形式化的数学理论和完整的Rust实现，我们建立了观察者模式的完整理论体系，为实际应用提供了坚实的理论基础和实现指导。
