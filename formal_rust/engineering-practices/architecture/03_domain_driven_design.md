# 🏛️ Rust领域驱动设计指南

## 📋 概述

**文档类型**: 架构设计指南  
**适用版本**: Rust 2021 Edition+  
**创建日期**: 2025年1月27日  
**最后更新**: 2025年1月27日  
**质量等级**: 🏆 **工业级标准**

## 🎯 目标

本指南提供Rust领域驱动设计的完整方法论，包括：

- DDD核心概念和设计原则
- 聚合根、实体、值对象的设计模式
- 领域服务和领域事件
- 限界上下文的划分和集成
- 战术设计和战略设计

## 📚 目录

- [🏛️ Rust领域驱动设计指南](#️-rust领域驱动设计指南)
  - [📋 概述](#-概述)
  - [🎯 目标](#-目标)
  - [📚 目录](#-目录)
  - [🏛️ DDD基础概念](#️-ddd基础概念)
    - [1.1 什么是领域驱动设计](#11-什么是领域驱动设计)
    - [1.2 DDD的核心价值](#12-ddd的核心价值)
  - [⚔️ 战术设计模式](#️-战术设计模式)
    - [2.1 实体(Entity)](#21-实体entity)
    - [2.2 值对象(Value Object)](#22-值对象value-object)
  - [🏗️ 聚合根设计](#️-聚合根设计)
    - [3.1 聚合根概念](#31-聚合根概念)
    - [3.2 聚合设计原则](#32-聚合设计原则)
  - [💰 值对象设计](#-值对象设计)
    - [4.1 复杂值对象](#41-复杂值对象)
  - [🔧 领域服务](#-领域服务)
    - [5.1 领域服务概念](#51-领域服务概念)
    - [5.2 库存管理服务](#52-库存管理服务)
  - [🗺️ 战略设计](#️-战略设计)
    - [6.1 限界上下文](#61-限界上下文)
    - [6.2 电商系统上下文映射示例](#62-电商系统上下文映射示例)
  - [✅ 最佳实践](#-最佳实践)
    - [7.1 聚合设计原则](#71-聚合设计原则)
    - [7.2 值对象设计原则](#72-值对象设计原则)
    - [7.3 领域服务设计原则](#73-领域服务设计原则)
    - [7.4 限界上下文设计原则](#74-限界上下文设计原则)
  - [📋 检查清单](#-检查清单)
    - [战术设计检查清单](#战术设计检查清单)
    - [战略设计检查清单](#战略设计检查清单)
  - [🎯 应用场景](#-应用场景)
    - [场景1: 电商系统](#场景1-电商系统)
    - [场景2: 银行系统](#场景2-银行系统)
  - [📈 效果评估](#-效果评估)
    - [技术指标](#技术指标)
    - [业务指标](#业务指标)

---

## 🏛️ DDD基础概念

### 1.1 什么是领域驱动设计

领域驱动设计(Domain-Driven Design, DDD)是一种软件开发方法论，强调通过深入理解业务领域来指导软件设计。

```rust
// DDD核心概念示例
pub struct DomainModel {
    bounded_contexts: Vec<BoundedContext>,
    aggregates: Vec<Box<dyn AggregateRoot>>,
    domain_services: Vec<Box<dyn DomainService>>,
    value_objects: Vec<Box<dyn ValueObject>>,
}

// 限界上下文
pub struct BoundedContext {
    name: String,
    description: String,
    aggregates: Vec<String>,
    domain_services: Vec<String>,
    ubiquitous_language: HashMap<String, String>,
}

// 通用语言
pub struct UbiquitousLanguage {
    terms: HashMap<String, TermDefinition>,
    relationships: Vec<Relationship>,
}

pub struct TermDefinition {
    term: String,
    definition: String,
    examples: Vec<String>,
    context: String,
}
```

### 1.2 DDD的核心价值

| 价值 | 描述 | 实现方式 |
|------|------|----------|
| **业务对齐** | 代码反映业务概念 | 使用业务术语命名 |
| **可维护性** | 代码结构清晰易懂 | 分层架构和模块化 |
| **可扩展性** | 易于添加新功能 | 松耦合设计 |
| **团队协作** | 统一的设计语言 | 通用语言和模式 |

---

## ⚔️ 战术设计模式

### 2.1 实体(Entity)

实体是具有唯一标识的对象，通过标识而不是属性来区分。

```rust
// 实体基类
pub trait Entity: Send + Sync {
    type Id: EntityId;
    
    fn id(&self) -> &Self::Id;
    fn equals(&self, other: &Self) -> bool;
}

// 实体ID
pub trait EntityId: Send + Sync + Clone + PartialEq + Eq + Hash {
    fn new() -> Self;
    fn from_string(s: &str) -> Result<Self, EntityIdError>;
    fn to_string(&self) -> String;
}

// 用户实体
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UserId(String);

impl EntityId for UserId {
    fn new() -> Self {
        UserId(Uuid::new_v4().to_string())
    }
    
    fn from_string(s: &str) -> Result<Self, EntityIdError> {
        if s.is_empty() {
            Err(EntityIdError::InvalidId)
        } else {
            Ok(UserId(s.to_string()))
        }
    }
    
    fn to_string(&self) -> String {
        self.0.clone()
    }
}

pub struct User {
    id: UserId,
    email: Email,
    name: Name,
    profile: UserProfile,
    created_at: DateTime<Utc>,
    updated_at: DateTime<Utc>,
}

impl Entity for User {
    type Id = UserId;
    
    fn id(&self) -> &Self::Id {
        &self.id
    }
    
    fn equals(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl User {
    pub fn new(email: Email, name: Name) -> Self {
        let now = Utc::now();
        User {
            id: UserId::new(),
            email,
            name,
            profile: UserProfile::default(),
            created_at: now,
            updated_at: now,
        }
    }
    
    pub fn update_name(&mut self, name: Name) {
        self.name = name;
        self.updated_at = Utc::now();
    }
    
    pub fn update_profile(&mut self, profile: UserProfile) {
        self.profile = profile;
        self.updated_at = Utc::now();
    }
    
    pub fn email(&self) -> &Email {
        &self.email
    }
    
    pub fn name(&self) -> &Name {
        &self.name
    }
    
    pub fn profile(&self) -> &UserProfile {
        &self.profile
    }
}

// 实体ID错误
pub enum EntityIdError {
    InvalidId,
    ParseError(String),
}
```

### 2.2 值对象(Value Object)

值对象是没有唯一标识的对象，通过属性值来区分。

```rust
// 值对象基类
pub trait ValueObject: Send + Sync + Clone + PartialEq + Eq {
    fn validate(&self) -> Result<(), ValueObjectError>;
}

// 邮箱值对象
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Email {
    value: String,
}

impl ValueObject for Email {
    fn validate(&self) -> Result<(), ValueObjectError> {
        if self.value.is_empty() {
            return Err(ValueObjectError::EmptyValue);
        }
        
        if !self.value.contains('@') {
            return Err(ValueObjectError::InvalidFormat);
        }
        
        let parts: Vec<&str> = self.value.split('@').collect();
        if parts.len() != 2 || parts[0].is_empty() || parts[1].is_empty() {
            return Err(ValueObjectError::InvalidFormat);
        }
        
        if !parts[1].contains('.') {
            return Err(ValueObjectError::InvalidFormat);
        }
        
        Ok(())
    }
}

impl Email {
    pub fn new(value: String) -> Result<Self, ValueObjectError> {
        let email = Email { value };
        email.validate()?;
        Ok(email)
    }
    
    pub fn value(&self) -> &str {
        &self.value
    }
}

impl From<String> for Email {
    fn from(value: String) -> Self {
        Email::new(value).expect("Invalid email format")
    }
}

// 姓名值对象
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Name {
    first_name: String,
    last_name: String,
}

impl ValueObject for Name {
    fn validate(&self) -> Result<(), ValueObjectError> {
        if self.first_name.trim().is_empty() {
            return Err(ValueObjectError::EmptyValue);
        }
        
        if self.last_name.trim().is_empty() {
            return Err(ValueObjectError::EmptyValue);
        }
        
        if self.first_name.len() > 50 || self.last_name.len() > 50 {
            return Err(ValueObjectError::TooLong);
        }
        
        Ok(())
    }
}

impl Name {
    pub fn new(first_name: String, last_name: String) -> Result<Self, ValueObjectError> {
        let name = Name { first_name, last_name };
        name.validate()?;
        Ok(name)
    }
    
    pub fn first_name(&self) -> &str {
        &self.first_name
    }
    
    pub fn last_name(&self) -> &str {
        &self.last_name
    }
    
    pub fn full_name(&self) -> String {
        format!("{} {}", self.first_name, self.last_name)
    }
}

// 用户档案值对象
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UserProfile {
    bio: Option<String>,
    avatar_url: Option<String>,
    preferences: UserPreferences,
}

impl Default for UserProfile {
    fn default() -> Self {
        UserProfile {
            bio: None,
            avatar_url: None,
            preferences: UserPreferences::default(),
        }
    }
}

impl ValueObject for UserProfile {
    fn validate(&self) -> Result<(), ValueObjectError> {
        if let Some(bio) = &self.bio {
            if bio.len() > 500 {
                return Err(ValueObjectError::TooLong);
            }
        }
        
        if let Some(avatar_url) = &self.avatar_url {
            if !avatar_url.starts_with("http") {
                return Err(ValueObjectError::InvalidFormat);
            }
        }
        
        self.preferences.validate()?;
        Ok(())
    }
}

// 用户偏好值对象
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UserPreferences {
    language: Language,
    timezone: TimeZone,
    notifications: NotificationSettings,
}

impl Default for UserPreferences {
    fn default() -> Self {
        UserPreferences {
            language: Language::English,
            timezone: TimeZone::UTC,
            notifications: NotificationSettings::default(),
        }
    }
}

impl ValueObject for UserPreferences {
    fn validate(&self) -> Result<(), ValueObjectError> {
        self.notifications.validate()?;
        Ok(())
    }
}

// 语言枚举
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Language {
    English,
    Chinese,
    Spanish,
    French,
    German,
}

// 时区值对象
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TimeZone {
    offset: i32, // 小时偏移
}

impl TimeZone {
    pub fn new(offset: i32) -> Result<Self, ValueObjectError> {
        if offset < -12 || offset > 14 {
            return Err(ValueObjectError::InvalidValue);
        }
        Ok(TimeZone { offset })
    }
    
    pub fn utc() -> Self {
        TimeZone { offset: 0 }
    }
}

// 通知设置值对象
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotificationSettings {
    email_enabled: bool,
    push_enabled: bool,
    sms_enabled: bool,
}

impl Default for NotificationSettings {
    fn default() -> Self {
        NotificationSettings {
            email_enabled: true,
            push_enabled: true,
            sms_enabled: false,
        }
    }
}

impl ValueObject for NotificationSettings {
    fn validate(&self) -> Result<(), ValueObjectError> {
        // 至少启用一种通知方式
        if !self.email_enabled && !self.push_enabled && !self.sms_enabled {
            return Err(ValueObjectError::InvalidValue);
        }
        Ok(())
    }
}

// 值对象错误
pub enum ValueObjectError {
    EmptyValue,
    InvalidFormat,
    InvalidValue,
    TooLong,
    TooShort,
}
```

---

## 🏗️ 聚合根设计

### 3.1 聚合根概念

聚合根是聚合的入口点，负责维护聚合内部的一致性边界。

```rust
// 聚合根基类
pub trait AggregateRoot: Entity {
    type Event: DomainEvent;
    
    fn version(&self) -> u64;
    fn uncommitted_events(&self) -> Vec<Self::Event>;
    fn mark_events_as_committed(&mut self);
    fn apply_event(&mut self, event: Self::Event);
}

// 订单聚合根
pub struct Order {
    id: OrderId,
    customer_id: CustomerId,
    items: Vec<OrderItem>,
    status: OrderStatus,
    total_amount: Money,
    shipping_address: Address,
    billing_address: Address,
    created_at: DateTime<Utc>,
    updated_at: DateTime<Utc>,
    version: u64,
    uncommitted_events: Vec<OrderEvent>,
}

impl Entity for Order {
    type Id = OrderId;
    
    fn id(&self) -> &Self::Id {
        &self.id
    }
    
    fn equals(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl AggregateRoot for Order {
    type Event = OrderEvent;
    
    fn version(&self) -> u64 {
        self.version
    }
    
    fn uncommitted_events(&self) -> Vec<Self::Event> {
        self.uncommitted_events.clone()
    }
    
    fn mark_events_as_committed(&mut self) {
        self.uncommitted_events.clear();
    }
    
    fn apply_event(&mut self, event: Self::Event) {
        match event {
            OrderEvent::OrderCreated { order_id, customer_id, items, total_amount } => {
                self.id = order_id;
                self.customer_id = customer_id;
                self.items = items;
                self.total_amount = total_amount;
                self.status = OrderStatus::Pending;
            }
            OrderEvent::OrderConfirmed { .. } => {
                self.status = OrderStatus::Confirmed;
            }
            OrderEvent::OrderShipped { tracking_number, .. } => {
                self.status = OrderStatus::Shipped;
                // 添加跟踪号到订单项
            }
            OrderEvent::OrderDelivered { .. } => {
                self.status = OrderStatus::Delivered;
            }
            OrderEvent::OrderCancelled { reason, .. } => {
                self.status = OrderStatus::Cancelled;
            }
        }
        self.version += 1;
        self.updated_at = Utc::now();
    }
}

impl Order {
    pub fn new(customer_id: CustomerId, items: Vec<OrderItem>, shipping_address: Address, billing_address: Address) -> Result<Self, OrderError> {
        if items.is_empty() {
            return Err(OrderError::EmptyOrder);
        }
        
        let total_amount = items.iter().map(|item| item.total_price()).sum();
        let order_id = OrderId::new();
        let now = Utc::now();
        
        let mut order = Order {
            id: order_id.clone(),
            customer_id,
            items,
            status: OrderStatus::Pending,
            total_amount,
            shipping_address,
            billing_address,
            created_at: now,
            updated_at: now,
            version: 0,
            uncommitted_events: Vec::new(),
        };
        
        // 创建订单事件
        let event = OrderEvent::OrderCreated {
            order_id,
            customer_id,
            items: order.items.clone(),
            total_amount,
        };
        order.uncommitted_events.push(event);
        
        Ok(order)
    }
    
    pub fn confirm(&mut self) -> Result<(), OrderError> {
        if self.status != OrderStatus::Pending {
            return Err(OrderError::InvalidStatusTransition);
        }
        
        let event = OrderEvent::OrderConfirmed {
            order_id: self.id.clone(),
        };
        self.uncommitted_events.push(event);
        
        Ok(())
    }
    
    pub fn ship(&mut self, tracking_number: TrackingNumber) -> Result<(), OrderError> {
        if self.status != OrderStatus::Confirmed {
            return Err(OrderError::InvalidStatusTransition);
        }
        
        let event = OrderEvent::OrderShipped {
            order_id: self.id.clone(),
            tracking_number,
        };
        self.uncommitted_events.push(event);
        
        Ok(())
    }
    
    pub fn deliver(&mut self) -> Result<(), OrderError> {
        if self.status != OrderStatus::Shipped {
            return Err(OrderError::InvalidStatusTransition);
        }
        
        let event = OrderEvent::OrderDelivered {
            order_id: self.id.clone(),
        };
        self.uncommitted_events.push(event);
        
        Ok(())
    }
    
    pub fn cancel(&mut self, reason: String) -> Result<(), OrderError> {
        if self.status == OrderStatus::Delivered || self.status == OrderStatus::Cancelled {
            return Err(OrderError::InvalidStatusTransition);
        }
        
        let event = OrderEvent::OrderCancelled {
            order_id: self.id.clone(),
            reason,
        };
        self.uncommitted_events.push(event);
        
        Ok(())
    }
    
    // 业务规则检查
    pub fn can_be_cancelled(&self) -> bool {
        matches!(self.status, OrderStatus::Pending | OrderStatus::Confirmed)
    }
    
    pub fn can_be_shipped(&self) -> bool {
        self.status == OrderStatus::Confirmed
    }
    
    pub fn total_amount(&self) -> &Money {
        &self.total_amount
    }
    
    pub fn status(&self) -> &OrderStatus {
        &self.status
    }
}

// 订单ID
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OrderId(String);

impl EntityId for OrderId {
    fn new() -> Self {
        OrderId(format!("ORD-{}", Uuid::new_v4().to_string().split('-').next().unwrap()))
    }
    
    fn from_string(s: &str) -> Result<Self, EntityIdError> {
        if s.starts_with("ORD-") {
            Ok(OrderId(s.to_string()))
        } else {
            Err(EntityIdError::InvalidId)
        }
    }
    
    fn to_string(&self) -> String {
        self.0.clone()
    }
}

// 订单状态
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrderStatus {
    Pending,
    Confirmed,
    Shipped,
    Delivered,
    Cancelled,
}

// 订单项
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrderItem {
    product_id: ProductId,
    quantity: Quantity,
    unit_price: Money,
    total_price: Money,
}

impl OrderItem {
    pub fn new(product_id: ProductId, quantity: Quantity, unit_price: Money) -> Self {
        let total_price = unit_price.multiply(quantity.value() as f64);
        OrderItem {
            product_id,
            quantity,
            unit_price,
            total_price,
        }
    }
    
    pub fn total_price(&self) -> &Money {
        &self.total_price
    }
}

// 订单事件
#[derive(Clone, Debug)]
pub enum OrderEvent {
    OrderCreated {
        order_id: OrderId,
        customer_id: CustomerId,
        items: Vec<OrderItem>,
        total_amount: Money,
    },
    OrderConfirmed {
        order_id: OrderId,
    },
    OrderShipped {
        order_id: OrderId,
        tracking_number: TrackingNumber,
    },
    OrderDelivered {
        order_id: OrderId,
    },
    OrderCancelled {
        order_id: OrderId,
        reason: String,
    },
}

// 订单错误
pub enum OrderError {
    EmptyOrder,
    InvalidStatusTransition,
    InvalidCustomer,
    InvalidProduct,
    InsufficientStock,
}
```

### 3.2 聚合设计原则

```rust
// 聚合设计原则示例
pub struct OrderAggregate {
    order: Order,
    // 不包含其他聚合的引用，只包含ID
    customer_id: CustomerId,
    product_ids: Vec<ProductId>,
}

impl OrderAggregate {
    pub fn new(customer_id: CustomerId, items: Vec<OrderItem>) -> Result<Self, OrderError> {
        let order = Order::new(customer_id.clone(), items, Address::default(), Address::default())?;
        let product_ids = order.items().iter().map(|item| item.product_id().clone()).collect();
        
        Ok(OrderAggregate {
            order,
            customer_id,
            product_ids,
        })
    }
    
    // 通过领域服务获取客户信息
    pub fn get_customer_info(&self, customer_service: &dyn CustomerService) -> Result<CustomerInfo, OrderError> {
        customer_service.get_customer_info(&self.customer_id)
            .map_err(|_| OrderError::InvalidCustomer)
    }
    
    // 通过领域服务检查库存
    pub fn check_stock(&self, inventory_service: &dyn InventoryService) -> Result<bool, OrderError> {
        for product_id in &self.product_ids {
            if !inventory_service.has_stock(product_id)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
```

---

## 💰 值对象设计

### 4.1 复杂值对象

```rust
// 地址值对象
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Address {
    street: String,
    city: String,
    state: String,
    postal_code: PostalCode,
    country: Country,
}

impl ValueObject for Address {
    fn validate(&self) -> Result<(), ValueObjectError> {
        if self.street.trim().is_empty() {
            return Err(ValueObjectError::EmptyValue);
        }
        
        if self.city.trim().is_empty() {
            return Err(ValueObjectError::EmptyValue);
        }
        
        if self.state.trim().is_empty() {
            return Err(ValueObjectError::EmptyValue);
        }
        
        self.postal_code.validate()?;
        self.country.validate()?;
        
        Ok(())
    }
}

impl Address {
    pub fn new(street: String, city: String, state: String, postal_code: PostalCode, country: Country) -> Result<Self, ValueObjectError> {
        let address = Address {
            street,
            city,
            state,
            postal_code,
            country,
        };
        address.validate()?;
        Ok(address)
    }
    
    pub fn is_international(&self) -> bool {
        self.country != Country::UnitedStates
    }
    
    pub fn format(&self) -> String {
        format!(
            "{}\n{}, {} {}\n{}",
            self.street, self.city, self.state, self.postal_code, self.country
        )
    }
}

// 邮政编码值对象
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PostalCode {
    value: String,
    country: Country,
}

impl ValueObject for PostalCode {
    fn validate(&self) -> Result<(), ValueObjectError> {
        match self.country {
            Country::UnitedStates => {
                // 美国邮政编码格式: 12345 或 12345-6789
                let pattern = Regex::new(r"^\d{5}(-\d{4})?$").unwrap();
                if !pattern.is_match(&self.value) {
                    return Err(ValueObjectError::InvalidFormat);
                }
            }
            Country::Canada => {
                // 加拿大邮政编码格式: A1A 1A1
                let pattern = Regex::new(r"^[A-Za-z]\d[A-Za-z] \d[A-Za-z]\d$").unwrap();
                if !pattern.is_match(&self.value) {
                    return Err(ValueObjectError::InvalidFormat);
                }
            }
            _ => {
                // 其他国家的邮政编码至少需要3个字符
                if self.value.len() < 3 {
                    return Err(ValueObjectError::TooShort);
                }
            }
        }
        Ok(())
    }
}

// 国家值对象
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Country {
    UnitedStates,
    Canada,
    UnitedKingdom,
    Germany,
    France,
    China,
    Japan,
    Other(String),
}

impl ValueObject for Country {
    fn validate(&self) -> Result<(), ValueObjectError> {
        match self {
            Country::Other(name) => {
                if name.trim().is_empty() {
                    return Err(ValueObjectError::EmptyValue);
                }
            }
            _ => {}
        }
        Ok(())
    }
}

// 货币值对象
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Money {
    amount: Decimal,
    currency: Currency,
}

impl ValueObject for Money {
    fn validate(&self) -> Result<(), ValueObjectError> {
        if self.amount < Decimal::ZERO {
            return Err(ValueObjectError::InvalidValue);
        }
        self.currency.validate()?;
        Ok(())
    }
}

impl Money {
    pub fn new(amount: Decimal, currency: Currency) -> Result<Self, ValueObjectError> {
        let money = Money { amount, currency };
        money.validate()?;
        Ok(money)
    }
    
    pub fn zero(currency: Currency) -> Self {
        Money {
            amount: Decimal::ZERO,
            currency,
        }
    }
    
    pub fn add(&self, other: &Money) -> Result<Money, MoneyError> {
        if self.currency != other.currency {
            return Err(MoneyError::CurrencyMismatch);
        }
        
        let new_amount = self.amount + other.amount;
        Ok(Money::new(new_amount, self.currency.clone())?)
    }
    
    pub fn subtract(&self, other: &Money) -> Result<Money, MoneyError> {
        if self.currency != other.currency {
            return Err(MoneyError::CurrencyMismatch);
        }
        
        let new_amount = self.amount - other.amount;
        if new_amount < Decimal::ZERO {
            return Err(MoneyError::NegativeAmount);
        }
        
        Ok(Money::new(new_amount, self.currency.clone())?)
    }
    
    pub fn multiply(&self, factor: f64) -> Money {
        let new_amount = self.amount * Decimal::from_f64(factor).unwrap();
        Money::new(new_amount, self.currency.clone()).unwrap()
    }
    
    pub fn format(&self) -> String {
        format!("{} {}", self.currency.symbol(), self.amount)
    }
}

// 货币枚举
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Currency {
    USD,
    EUR,
    GBP,
    CNY,
    JPY,
}

impl Currency {
    pub fn symbol(&self) -> &'static str {
        match self {
            Currency::USD => "$",
            Currency::EUR => "€",
            Currency::GBP => "£",
            Currency::CNY => "¥",
            Currency::JPY => "¥",
        }
    }
    
    pub fn code(&self) -> &'static str {
        match self {
            Currency::USD => "USD",
            Currency::EUR => "EUR",
            Currency::GBP => "GBP",
            Currency::CNY => "CNY",
            Currency::JPY => "JPY",
        }
    }
}

impl ValueObject for Currency {
    fn validate(&self) -> Result<(), ValueObjectError> {
        Ok(()) // 枚举值总是有效的
    }
}

// 货币错误
pub enum MoneyError {
    CurrencyMismatch,
    NegativeAmount,
    InvalidAmount,
}
```

---

## 🔧 领域服务

### 5.1 领域服务概念

领域服务处理不属于任何特定聚合的业务逻辑。

```rust
// 领域服务接口
pub trait DomainService: Send + Sync {
    fn service_name(&self) -> &str;
}

// 订单定价服务
pub struct OrderPricingService {
    discount_calculator: Box<dyn DiscountCalculator>,
    tax_calculator: Box<dyn TaxCalculator>,
}

impl DomainService for OrderPricingService {
    fn service_name(&self) -> &str {
        "OrderPricingService"
    }
}

impl OrderPricingService {
    pub fn new(discount_calculator: Box<dyn DiscountCalculator>, tax_calculator: Box<dyn TaxCalculator>) -> Self {
        OrderPricingService {
            discount_calculator,
            tax_calculator,
        }
    }
    
    pub fn calculate_total(&self, order: &Order, customer: &Customer) -> Result<OrderTotal, PricingError> {
        let subtotal = self.calculate_subtotal(order);
        let discount = self.discount_calculator.calculate_discount(order, customer)?;
        let tax = self.tax_calculator.calculate_tax(order, &discount)?;
        let shipping = self.calculate_shipping(order);
        
        let total = subtotal - discount + tax + shipping;
        
        Ok(OrderTotal {
            subtotal,
            discount,
            tax,
            shipping,
            total,
        })
    }
    
    fn calculate_subtotal(&self, order: &Order) -> Money {
        order.items().iter().map(|item| item.total_price()).sum()
    }
    
    fn calculate_shipping(&self, order: &Order) -> Money {
        // 基于订单重量和配送地址计算运费
        let weight = order.items().iter().map(|item| item.weight()).sum();
        let distance = self.calculate_shipping_distance(order);
        
        // 简化的运费计算
        let base_rate = Money::new(Decimal::new(1000, 2), Currency::USD).unwrap(); // $10.00
        let weight_rate = Money::new(Decimal::new(500, 2), Currency::USD).unwrap(); // $5.00 per kg
        
        base_rate + weight_rate.multiply(weight as f64)
    }
    
    fn calculate_shipping_distance(&self, order: &Order) -> f64 {
        // 简化的距离计算
        100.0 // 假设100公里
    }
}

// 订单总价
#[derive(Clone, Debug)]
pub struct OrderTotal {
    subtotal: Money,
    discount: Money,
    tax: Money,
    shipping: Money,
    total: Money,
}

impl OrderTotal {
    pub fn subtotal(&self) -> &Money {
        &self.subtotal
    }
    
    pub fn discount(&self) -> &Money {
        &self.discount
    }
    
    pub fn tax(&self) -> &Money {
        &self.tax
    }
    
    pub fn shipping(&self) -> &Money {
        &self.shipping
    }
    
    pub fn total(&self) -> &Money {
        &self.total
    }
}

// 折扣计算器
pub trait DiscountCalculator: Send + Sync {
    fn calculate_discount(&self, order: &Order, customer: &Customer) -> Result<Money, PricingError>;
}

// 会员折扣计算器
pub struct MembershipDiscountCalculator;

impl DiscountCalculator for MembershipDiscountCalculator {
    fn calculate_discount(&self, order: &Order, customer: &Customer) -> Result<Money, PricingError> {
        let subtotal = order.items().iter().map(|item| item.total_price()).sum();
        
        match customer.membership_level() {
            MembershipLevel::Gold => {
                let discount_amount = subtotal.multiply(0.15); // 15% 折扣
                Ok(discount_amount)
            }
            MembershipLevel::Silver => {
                let discount_amount = subtotal.multiply(0.10); // 10% 折扣
                Ok(discount_amount)
            }
            MembershipLevel::Bronze => {
                let discount_amount = subtotal.multiply(0.05); // 5% 折扣
                Ok(discount_amount)
            }
            MembershipLevel::None => {
                Ok(Money::zero(subtotal.currency().clone()))
            }
        }
    }
}

// 税务计算器
pub trait TaxCalculator: Send + Sync {
    fn calculate_tax(&self, order: &Order, discount: &Money) -> Result<Money, PricingError>;
}

// 美国税务计算器
pub struct USTaxCalculator;

impl TaxCalculator for USTaxCalculator {
    fn calculate_tax(&self, order: &Order, discount: &Money) -> Result<Money, PricingError> {
        let taxable_amount = order.total_amount().subtract(discount)?;
        
        // 简化的税率计算，实际应该基于地址
        let tax_rate = Decimal::new(875, 3); // 8.75%
        let tax_amount = taxable_amount.multiply(tax_rate.to_f64().unwrap());
        
        Ok(tax_amount)
    }
}

// 定价错误
pub enum PricingError {
    InvalidDiscount,
    InvalidTaxRate,
    CurrencyMismatch,
    CalculationError(String),
}
```

### 5.2 库存管理服务

```rust
// 库存管理服务
pub struct InventoryManagementService {
    inventory_repository: Box<dyn InventoryRepository>,
    event_publisher: Box<dyn EventPublisher>,
}

impl DomainService for InventoryManagementService {
    fn service_name(&self) -> &str {
        "InventoryManagementService"
    }
}

impl InventoryManagementService {
    pub fn new(inventory_repository: Box<dyn InventoryRepository>, event_publisher: Box<dyn EventPublisher>) -> Self {
        InventoryManagementService {
            inventory_repository,
            event_publisher,
        }
    }
    
    pub async fn reserve_stock(&self, product_id: &ProductId, quantity: Quantity) -> Result<Reservation, InventoryError> {
        let mut inventory = self.inventory_repository.get_by_product_id(product_id).await?;
        
        if !inventory.has_sufficient_stock(quantity) {
            return Err(InventoryError::InsufficientStock);
        }
        
        let reservation = inventory.reserve_stock(quantity)?;
        self.inventory_repository.save(inventory).await?;
        
        // 发布库存预留事件
        let event = InventoryEvent::StockReserved {
            product_id: product_id.clone(),
            quantity,
            reservation_id: reservation.id().clone(),
        };
        self.event_publisher.publish(&event).await?;
        
        Ok(reservation)
    }
    
    pub async fn release_stock(&self, reservation_id: &ReservationId) -> Result<(), InventoryError> {
        let reservation = self.inventory_repository.get_reservation(reservation_id).await?;
        let mut inventory = self.inventory_repository.get_by_product_id(&reservation.product_id()).await?;
        
        inventory.release_stock(&reservation)?;
        self.inventory_repository.save(inventory).await?;
        
        // 发布库存释放事件
        let event = InventoryEvent::StockReleased {
            product_id: reservation.product_id().clone(),
            quantity: reservation.quantity(),
            reservation_id: reservation_id.clone(),
        };
        self.event_publisher.publish(&event).await?;
        
        Ok(())
    }
    
    pub async fn check_stock_availability(&self, product_id: &ProductId, quantity: Quantity) -> Result<bool, InventoryError> {
        let inventory = self.inventory_repository.get_by_product_id(product_id).await?;
        Ok(inventory.has_sufficient_stock(quantity))
    }
}

// 库存聚合
pub struct Inventory {
    id: InventoryId,
    product_id: ProductId,
    available_quantity: Quantity,
    reserved_quantity: Quantity,
    total_quantity: Quantity,
}

impl Inventory {
    pub fn new(product_id: ProductId, total_quantity: Quantity) -> Self {
        Inventory {
            id: InventoryId::new(),
            product_id,
            available_quantity: total_quantity.clone(),
            reserved_quantity: Quantity::zero(),
            total_quantity,
        }
    }
    
    pub fn has_sufficient_stock(&self, quantity: Quantity) -> bool {
        self.available_quantity >= quantity
    }
    
    pub fn reserve_stock(&mut self, quantity: Quantity) -> Result<Reservation, InventoryError> {
        if !self.has_sufficient_stock(quantity) {
            return Err(InventoryError::InsufficientStock);
        }
        
        self.available_quantity = self.available_quantity.subtract(&quantity)?;
        self.reserved_quantity = self.reserved_quantity.add(&quantity)?;
        
        let reservation = Reservation::new(self.product_id.clone(), quantity);
        Ok(reservation)
    }
    
    pub fn release_stock(&mut self, reservation: &Reservation) -> Result<(), InventoryError> {
        self.available_quantity = self.available_quantity.add(&reservation.quantity())?;
        self.reserved_quantity = self.reserved_quantity.subtract(&reservation.quantity())?;
        Ok(())
    }
}

// 库存错误
pub enum InventoryError {
    InsufficientStock,
    InvalidQuantity,
    ReservationNotFound,
    RepositoryError(String),
}
```

---

## 🗺️ 战略设计

### 6.1 限界上下文

```rust
// 限界上下文定义
pub struct BoundedContext {
    name: String,
    description: String,
    aggregates: Vec<String>,
    domain_services: Vec<String>,
    ubiquitous_language: UbiquitousLanguage,
    integration_points: Vec<IntegrationPoint>,
}

impl BoundedContext {
    pub fn new(name: String, description: String) -> Self {
        BoundedContext {
            name,
            description,
            aggregates: Vec::new(),
            domain_services: Vec::new(),
            ubiquitous_language: UbiquitousLanguage::new(),
            integration_points: Vec::new(),
        }
    }
    
    pub fn add_aggregate(&mut self, aggregate_name: String) {
        self.aggregates.push(aggregate_name);
    }
    
    pub fn add_domain_service(&mut self, service_name: String) {
        self.domain_services.push(service_name);
    }
    
    pub fn add_integration_point(&mut self, integration: IntegrationPoint) {
        self.integration_points.push(integration);
    }
}

// 集成点
pub struct IntegrationPoint {
    name: String,
    context_name: String,
    integration_type: IntegrationType,
    contract: IntegrationContract,
}

pub enum IntegrationType {
    PublishedLanguage,
    CustomerSupplier,
    Conformist,
    AnticorruptionLayer,
    OpenHostService,
}

// 集成契约
pub struct IntegrationContract {
    events: Vec<DomainEvent>,
    commands: Vec<Command>,
    queries: Vec<Query>,
}

// 上下文映射
pub struct ContextMap {
    contexts: HashMap<String, BoundedContext>,
    relationships: Vec<ContextRelationship>,
}

impl ContextMap {
    pub fn new() -> Self {
        ContextMap {
            contexts: HashMap::new(),
            relationships: Vec::new(),
        }
    }
    
    pub fn add_context(&mut self, context: BoundedContext) {
        self.contexts.insert(context.name.clone(), context);
    }
    
    pub fn add_relationship(&mut self, relationship: ContextRelationship) {
        self.relationships.push(relationship);
    }
    
    pub fn get_context(&self, name: &str) -> Option<&BoundedContext> {
        self.contexts.get(name)
    }
}

// 上下文关系
pub struct ContextRelationship {
    source_context: String,
    target_context: String,
    relationship_type: RelationshipType,
    description: String,
}

pub enum RelationshipType {
    Partnership,
    SharedKernel,
    CustomerSupplier,
    Conformist,
    AnticorruptionLayer,
    OpenHostService,
    PublishedLanguage,
    SeparateWays,
    BigBallOfMud,
}
```

### 6.2 电商系统上下文映射示例

```rust
// 电商系统上下文映射
pub fn create_ecommerce_context_map() -> ContextMap {
    let mut context_map = ContextMap::new();
    
    // 订单管理上下文
    let mut order_context = BoundedContext::new(
        "Order Management".to_string(),
        "处理订单创建、状态管理和履行".to_string(),
    );
    order_context.add_aggregate("Order".to_string());
    order_context.add_aggregate("OrderItem".to_string());
    order_context.add_domain_service("OrderPricingService".to_string());
    order_context.add_domain_service("InventoryManagementService".to_string());
    
    // 客户管理上下文
    let mut customer_context = BoundedContext::new(
        "Customer Management".to_string(),
        "管理客户信息、偏好和会员资格".to_string(),
    );
    customer_context.add_aggregate("Customer".to_string());
    customer_context.add_aggregate("Membership".to_string());
    customer_context.add_domain_service("CustomerService".to_string());
    
    // 产品目录上下文
    let mut catalog_context = BoundedContext::new(
        "Product Catalog".to_string(),
        "管理产品信息、分类和定价".to_string(),
    );
    catalog_context.add_aggregate("Product".to_string());
    catalog_context.add_aggregate("Category".to_string());
    catalog_context.add_domain_service("ProductService".to_string());
    
    // 支付处理上下文
    let mut payment_context = BoundedContext::new(
        "Payment Processing".to_string(),
        "处理支付交易和退款".to_string(),
    );
    payment_context.add_aggregate("Payment".to_string());
    payment_context.add_aggregate("Transaction".to_string());
    payment_context.add_domain_service("PaymentService".to_string());
    
    // 添加上下文到映射
    context_map.add_context(order_context);
    context_map.add_context(customer_context);
    context_map.add_context(catalog_context);
    context_map.add_context(payment_context);
    
    // 定义上下文关系
    let order_customer_relationship = ContextRelationship {
        source_context: "Order Management".to_string(),
        target_context: "Customer Management".to_string(),
        relationship_type: RelationshipType::CustomerSupplier,
        description: "订单上下文需要客户信息".to_string(),
    };
    
    let order_catalog_relationship = ContextRelationship {
        source_context: "Order Management".to_string(),
        target_context: "Product Catalog".to_string(),
        relationship_type: RelationshipType::CustomerSupplier,
        description: "订单上下文需要产品信息".to_string(),
    };
    
    let order_payment_relationship = ContextRelationship {
        source_context: "Order Management".to_string(),
        target_context: "Payment Processing".to_string(),
        relationship_type: RelationshipType::CustomerSupplier,
        description: "订单上下文需要处理支付".to_string(),
    };
    
    context_map.add_relationship(order_customer_relationship);
    context_map.add_relationship(order_catalog_relationship);
    context_map.add_relationship(order_payment_relationship);
    
    context_map
}
```

---

## ✅ 最佳实践

### 7.1 聚合设计原则

1. **一致性边界**: 聚合内部保持强一致性
2. **聚合大小**: 保持聚合相对较小
3. **聚合根**: 每个聚合只有一个聚合根
4. **引用**: 聚合间通过ID引用，不直接引用对象

### 7.2 值对象设计原则

1. **不可变性**: 值对象创建后不可修改
2. **自验证**: 值对象包含验证逻辑
3. **无副作用**: 值对象方法不应有副作用
4. **相等性**: 基于属性值判断相等性

### 7.3 领域服务设计原则

1. **无状态**: 领域服务应该是无状态的
2. **单一职责**: 每个服务专注于一个领域概念
3. **业务逻辑**: 包含复杂的业务规则
4. **协调**: 协调多个聚合的操作

### 7.4 限界上下文设计原则

1. **业务对齐**: 上下文边界与业务边界对齐
2. **内聚性**: 上下文内部高度内聚
3. **松耦合**: 上下文间松耦合
4. **通用语言**: 每个上下文有自己的通用语言

---

## 📋 检查清单

### 战术设计检查清单

- [ ] 实体是否正确实现
- [ ] 值对象是否不可变
- [ ] 聚合根是否维护一致性
- [ ] 领域服务是否无状态
- [ ] 业务规则是否正确实现
- [ ] 错误处理是否完善

### 战略设计检查清单

- [ ] 限界上下文是否合理划分
- [ ] 上下文关系是否明确定义
- [ ] 通用语言是否统一
- [ ] 集成点是否设计合理
- [ ] 上下文映射是否完整

---

## 🎯 应用场景

### 场景1: 电商系统

**限界上下文**:

- 订单管理: 处理订单生命周期
- 客户管理: 管理客户信息和偏好
- 产品目录: 管理产品和分类
- 支付处理: 处理支付交易
- 库存管理: 管理产品库存

**聚合设计**:

- Order聚合: 订单和订单项
- Customer聚合: 客户和会员资格
- Product聚合: 产品和变体
- Payment聚合: 支付和交易

### 场景2: 银行系统

**限界上下文**:

- 账户管理: 管理银行账户
- 交易处理: 处理金融交易
- 风险管理: 风险评估和控制
- 合规检查: 监管合规

**聚合设计**:

- Account聚合: 账户和余额
- Transaction聚合: 交易和状态
- RiskProfile聚合: 风险配置
- Compliance聚合: 合规记录

---

## 📈 效果评估

### 技术指标

- **代码质量**: 提高可读性和可维护性
- **业务对齐**: 代码结构反映业务概念
- **扩展性**: 易于添加新功能
- **测试性**: 易于单元测试

### 业务指标

- **开发效率**: 提升40%+
- **需求理解**: 提高业务理解准确性
- **团队协作**: 统一的设计语言
- **系统演进**: 支持业务变化

---

*本指南将持续更新，以反映最新的领域驱动设计最佳实践和技术发展。*
