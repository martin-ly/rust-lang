# 代理模式 (Proxy Pattern) - 形式化重构

## 目录 (Table of Contents)

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

代理模式是一种结构型设计模式，为其他对象提供一个代替或占位符，以控制对它的访问。

**核心思想**：

- 提供一个代理对象来控制对目标对象的访问
- 在访问目标对象时引入额外的控制层
- 支持延迟加载、访问控制、缓存等功能

### 1.2 模式结构

```text
┌─────────────────┐    ┌──────────────────┐    ┌─────────────────────┐
│   Client        │    │  Subject         │    │  RealSubject        │
│                 │    │                  │    │                     │
│ - request()     │◄──►│ + request()      │◄──►│ + request()         │
│                 │    │                  │    │                     │
└─────────────────┘    └──────────────────┘    └─────────────────────┘
                                ▲
                                │
                       ┌──────────────────┐
                       │     Proxy        │
                       │                  │
                       │ - realSubject    │
                       │ + request()      │
                       └──────────────────┘
```

## 2. 形式化定义

### 2.1 代理模式五元组

设代理模式为五元组 $P = (S, P, I, O, C)$，其中：

- $S$ 是主体集合 (Subject)
- $P$ 是代理集合 (Proxy)
- $I$ 是接口集合 (Interface)
- $O$ 是操作集合 (Operations)
- $C$ 是控制策略集合 (Control Strategies)

### 2.2 数学关系定义

**定义1.2.1 (代理关系)**
对于主体 $s \in S$ 和代理 $p \in P$，定义代理关系 $R \subseteq S \times P$：

- $(s, p) \in R$ 表示代理 $p$ 代表主体 $s$

**定义1.2.2 (接口映射)**
对于接口 $i \in I$，定义接口映射函数 $M: I \rightarrow (S \cup P)$：

- $M(i) = x$ 表示接口 $i$ 由 $x$ 实现

**定义1.2.3 (操作拦截)**
对于操作 $o \in O$ 和代理 $p \in P$，定义拦截函数 $I: P \times O \rightarrow O$：

- $I(p, o) = p.pre(o) \circ o \circ p.post(o)$

## 3. 数学理论

### 3.1 代理控制理论

**公理2.1.1 (代理控制公理)**

1. **接口一致性**: 代理与主体实现相同的接口
2. **透明性**: 客户端无法区分代理和主体
3. **控制性**: 代理可以控制对主体的访问

**定理2.1.1 (代理控制正确性)**
如果代理模式 $P$ 满足代理控制公理，则：

- 代理可以透明地替代主体
- 代理可以控制访问策略
- 代理可以添加额外功能

**证明**:

1. 由接口一致性公理，代理实现相同接口
2. 由透明性公理，客户端无法区分
3. 由控制性公理，代理可以控制访问

### 3.2 访问控制理论

**公理2.2.1 (访问控制公理)**
对于代理 $p \in P$ 和主体 $s \in S$：

- 代理可以验证访问权限
- 代理可以记录访问日志
- 代理可以限制访问频率

**定理2.2.1 (访问控制正确性)**
如果代理 $p$ 满足访问控制公理，则：

- 访问控制是安全的
- 访问日志是完整的
- 访问限制是有效的

### 3.3 延迟加载理论

**定义2.3.1 (延迟加载)**
对于主体 $s \in S$，延迟加载函数 $L: S \rightarrow S$ 定义为：

- $L(s) = s'$ 其中 $s'$ 是延迟加载的主体

**定理2.3.1 (延迟加载正确性)**
对于任意主体 $s \in S$：

- 延迟加载是透明的
- 延迟加载是高效的
- 延迟加载是安全的

## 4. 核心定理

### 4.1 代理模式正确性定理

**定理3.1.1 (接口一致性)**
对于代理模式 $P = (S, P, I, O, C)$，如果满足：

1. 代理与主体实现相同接口
2. 代理可以透明替代主体
3. 代理可以控制访问策略

则代理模式接口一致。

**证明**:

1. 由定义1.2.1，代理关系定义正确
2. 由公理2.1.1，代理控制公理成立
3. 由定义1.2.2，接口映射定义正确

### 4.2 访问控制定理

**定理3.2.1 (访问控制完整性)**
对于代理 $p \in P$ 和操作 $o \in O$：

- 代理可以验证访问权限
- 代理可以记录访问日志
- 代理可以限制访问频率

**证明**:

1. 由公理2.2.1，访问控制公理成立
2. 由定义1.2.3，操作拦截定义正确
3. 因此访问控制完整

### 4.3 性能优化定理

**定理3.3.1 (代理性能)**
对于代理模式 $P$ 中的操作：

- 缓存命中：$O(1)$ 访问时间
- 缓存未命中：$O(1)$ 代理开销 + 主体操作时间
- 内存使用：$O(|P| + |S|)$

**证明**:

1. 缓存命中是直接访问
2. 缓存未命中需要代理处理
3. 内存使用包括代理和主体

### 4.4 安全性定理

**定理3.4.1 (代理安全性)**
对于代理模式 $P$：

- 代理可以验证访问权限
- 代理可以记录所有访问
- 代理可以防止未授权访问

**证明**:

1. 由访问控制公理，权限验证成立
2. 由操作拦截定义，访问记录成立
3. 由控制策略，安全防护成立

## 5. Rust实现

### 5.1 基础实现

```rust
// 主体接口
pub trait Subject {
    fn request(&self) -> String;
}

// 具体主体
pub struct RealSubject {
    name: String,
}

impl RealSubject {
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

impl Subject for RealSubject {
    fn request(&self) -> String {
        format!("RealSubject[{}]: Handling request", self.name)
    }
}

// 代理
pub struct Proxy {
    real_subject: Option<RealSubject>,
    name: String,
}

impl Proxy {
    pub fn new(name: String) -> Self {
        Self {
            real_subject: None,
            name,
        }
    }
    
    fn lazy_init(&mut self) {
        if self.real_subject.is_none() {
            self.real_subject = Some(RealSubject::new(self.name.clone()));
        }
    }
}

impl Subject for Proxy {
    fn request(&self) -> String {
        // 这里需要可变引用，但trait方法不允许
        // 实际实现中可以使用内部可变性
        format!("Proxy[{}]: Request intercepted", self.name)
    }
}

// 使用内部可变性的代理
use std::cell::RefCell;

pub struct SmartProxy {
    real_subject: RefCell<Option<RealSubject>>,
    name: String,
}

impl SmartProxy {
    pub fn new(name: String) -> Self {
        Self {
            real_subject: RefCell::new(None),
            name,
        }
    }
    
    fn lazy_init(&self) {
        let mut subject = self.real_subject.borrow_mut();
        if subject.is_none() {
            *subject = Some(RealSubject::new(self.name.clone()));
        }
    }
}

impl Subject for SmartProxy {
    fn request(&self) -> String {
        self.lazy_init();
        
        let subject = self.real_subject.borrow();
        if let Some(ref real_subject) = *subject {
            format!("SmartProxy[{}]: {}", self.name, real_subject.request())
        } else {
            format!("SmartProxy[{}]: No subject available", self.name)
        }
    }
}
```

### 5.2 泛型实现

```rust
use std::cell::RefCell;
use std::fmt::Display;

// 泛型主体接口
pub trait GenericSubject<T: Display + Clone> {
    fn request(&self, data: T) -> String;
}

// 泛型具体主体
pub struct GenericRealSubject<T: Display + Clone> {
    name: String,
    _phantom: std::marker::PhantomData<T>,
}

impl<T: Display + Clone> GenericRealSubject<T> {
    pub fn new(name: String) -> Self {
        Self {
            name,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T: Display + Clone> GenericSubject<T> for GenericRealSubject<T> {
    fn request(&self, data: T) -> String {
        format!("GenericRealSubject[{}]: Handling request with data: {}", 
                self.name, data)
    }
}

// 泛型代理
pub struct GenericProxy<T: Display + Clone> {
    real_subject: RefCell<Option<GenericRealSubject<T>>>,
    name: String,
    cache: RefCell<std::collections::HashMap<T, String>>,
}

impl<T: Display + Clone + std::hash::Hash + Eq> GenericProxy<T> {
    pub fn new(name: String) -> Self {
        Self {
            real_subject: RefCell::new(None),
            name,
            cache: RefCell::new(std::collections::HashMap::new()),
        }
    }
    
    fn lazy_init(&self) {
        let mut subject = self.real_subject.borrow_mut();
        if subject.is_none() {
            *subject = Some(GenericRealSubject::new(self.name.clone()));
        }
    }
}

impl<T: Display + Clone + std::hash::Hash + Eq> GenericSubject<T> for GenericProxy<T> {
    fn request(&self, data: T) -> String {
        // 检查缓存
        {
            let cache = self.cache.borrow();
            if let Some(cached_result) = cache.get(&data) {
                return format!("GenericProxy[{}]: Cached result: {}", 
                              self.name, cached_result);
            }
        }
        
        // 延迟初始化
        self.lazy_init();
        
        // 执行请求
        let subject = self.real_subject.borrow();
        if let Some(ref real_subject) = *subject {
            let result = real_subject.request(data.clone());
            
            // 缓存结果
            {
                let mut cache = self.cache.borrow_mut();
                cache.insert(data, result.clone());
            }
            
            format!("GenericProxy[{}]: {}", self.name, result)
        } else {
            format!("GenericProxy[{}]: No subject available", self.name)
        }
    }
}
```

### 5.3 虚拟代理实现

```rust
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

// 图片接口
trait Image {
    fn display(&self);
    fn get_size(&self) -> (u32, u32);
}

// 真实图片
struct RealImage {
    filename: String,
    width: u32,
    height: u32,
    loaded: bool,
}

impl RealImage {
    fn new(filename: String) -> Self {
        println!("Loading image: {}", filename);
        // 模拟图片加载
        RealImage {
            filename,
            width: 1920,
            height: 1080,
            loaded: true,
        }
    }
}

impl Image for RealImage {
    fn display(&self) {
        println!("Displaying image: {} ({}x{})", self.filename, self.width, self.height);
    }

    fn get_size(&self) -> (u32, u32) {
        (self.width, self.height)
    }
}

// 图片代理
struct ImageProxy {
    filename: String,
    real_image: Arc<Mutex<Option<RealImage>>>,
}

impl ImageProxy {
    fn new(filename: String) -> Self {
        ImageProxy {
            filename,
            real_image: Arc::new(Mutex::new(None)),
        }
    }

    fn load_image(&self) {
        let mut guard = self.real_image.lock().unwrap();
        if guard.is_none() {
            *guard = Some(RealImage::new(self.filename.clone()));
        }
    }
}

impl Image for ImageProxy {
    fn display(&self) {
        self.load_image();
        if let Some(ref image) = *self.real_image.lock().unwrap() {
            image.display();
        }
    }

    fn get_size(&self) -> (u32, u32) {
        self.load_image();
        if let Some(ref image) = *self.real_image.lock().unwrap() {
            image.get_size()
        } else {
            (0, 0)
        }
    }
}

// 图片查看器
struct ImageViewer {
    images: Vec<Arc<dyn Image>>,
}

impl ImageViewer {
    fn new() -> Self {
        ImageViewer {
            images: Vec::new(),
        }
    }

    fn add_image(&mut self, image: Arc<dyn Image>) {
        self.images.push(image);
    }

    fn display_all(&self) {
        for image in &self.images {
            image.display();
        }
    }
}
```

### 5.4 保护代理实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

// 保护代理 - 用于访问控制
struct ProtectionProxy {
    real_subject: Option<Arc<RealSubject>>,
    permissions: HashMap<String, Vec<String>>,
}

impl ProtectionProxy {
    fn new() -> Self {
        let mut permissions = HashMap::new();
        permissions.insert("admin".to_string(), vec!["read".to_string(), "write".to_string()]);
        permissions.insert("user".to_string(), vec!["read".to_string()]);
        permissions.insert("guest".to_string(), vec![]);

        ProtectionProxy {
            real_subject: None,
            permissions,
        }
    }

    fn check_permission(&self, user: &str, operation: &str) -> bool {
        if let Some(user_permissions) = self.permissions.get(user) {
            user_permissions.contains(&operation.to_string())
        } else {
            false
        }
    }

    fn lazy_init(&mut self) {
        if self.real_subject.is_none() {
            self.real_subject = Some(Arc::new(RealSubject::new()));
        }
    }
}

impl Subject for ProtectionProxy {
    fn request(&self, data: &str) -> String {
        // 解析请求格式: "user:operation:data"
        let parts: Vec<&str> = data.split(':').collect();
        if parts.len() != 3 {
            return "Invalid request format".to_string();
        }

        let user = parts[0];
        let operation = parts[1];
        let actual_data = parts[2];

        // 检查权限
        if !self.check_permission(user, operation) {
            return format!("Access denied for user '{}' to operation '{}'", user, operation);
        }

        // 延迟初始化
        let mut proxy = ProtectionProxy {
            real_subject: self.real_subject.clone(),
            permissions: self.permissions.clone(),
        };
        proxy.lazy_init();

        // 委托给真实主题
        if let Some(ref real_subject) = proxy.real_subject {
            real_subject.request(actual_data)
        } else {
            "Error: RealSubject not initialized".to_string()
        }
    }
}
```

### 5.5 缓存代理实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};

// 缓存条目
struct CacheEntry {
    data: String,
    timestamp: Instant,
    ttl: Duration,
}

impl CacheEntry {
    fn new(data: String, ttl: Duration) -> Self {
        CacheEntry {
            data,
            timestamp: Instant::now(),
            ttl,
        }
    }

    fn is_expired(&self) -> bool {
        self.timestamp.elapsed() > self.ttl
    }
}

// 缓存代理
struct CacheProxy {
    real_subject: Option<Arc<RealSubject>>,
    cache: Arc<RwLock<HashMap<String, CacheEntry>>>,
    ttl: Duration,
}

impl CacheProxy {
    fn new(ttl: Duration) -> Self {
        CacheProxy {
            real_subject: None,
            cache: Arc::new(RwLock::new(HashMap::new())),
            ttl,
        }
    }

    fn lazy_init(&mut self) {
        if self.real_subject.is_none() {
            self.real_subject = Some(Arc::new(RealSubject::new()));
        }
    }

    fn cleanup_expired(&self) {
        let mut cache = self.cache.write().unwrap();
        cache.retain(|_, entry| !entry.is_expired());
    }
}

impl Subject for CacheProxy {
    fn request(&self, data: &str) -> String {
        // 清理过期缓存
        self.cleanup_expired();

        // 检查缓存
        {
            let cache = self.cache.read().unwrap();
            if let Some(entry) = cache.get(data) {
                if !entry.is_expired() {
                    println!("CacheProxy: Returning cached result");
                    return entry.data.clone();
                }
            }
        }

        // 延迟初始化
        let mut proxy = CacheProxy {
            real_subject: self.real_subject.clone(),
            cache: Arc::clone(&self.cache),
            ttl: self.ttl,
        };
        proxy.lazy_init();

        // 委托给真实主题
        if let Some(ref real_subject) = proxy.real_subject {
            let result = real_subject.request(data);

            // 缓存结果
            {
                let mut cache = self.cache.write().unwrap();
                cache.insert(data.to_string(), CacheEntry::new(result.clone(), self.ttl));
            }

            result
        } else {
            "Error: RealSubject not initialized".to_string()
        }
    }
}
```

### 5.6 远程代理实现

```rust
use std::sync::{Arc, Mutex};
use tokio::net::TcpStream;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

// 远程代理 - 用于网络通信
struct RemoteProxy {
    real_subject: Option<Arc<RealSubject>>,
    server_address: String,
    connection: Arc<Mutex<Option<TcpStream>>>,
}

impl RemoteProxy {
    fn new(server_address: String) -> Self {
        RemoteProxy {
            real_subject: None,
            server_address,
            connection: Arc::new(Mutex::new(None)),
        }
    }

    async fn connect(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut connection = self.connection.lock().unwrap();
        if connection.is_none() {
            println!("RemoteProxy: Connecting to {}", self.server_address);
            let stream = TcpStream::connect(&self.server_address).await?;
            *connection = Some(stream);
        }
        Ok(())
    }

    async fn send_request(&self, data: &str) -> Result<String, Box<dyn std::error::Error>> {
        self.connect().await?;

        let mut connection = self.connection.lock().unwrap();
        if let Some(ref mut stream) = *connection {
            // 发送请求
            stream.write_all(data.as_bytes()).await?;

            // 接收响应
            let mut buffer = [0; 1024];
            let n = stream.read(&mut buffer).await?;
            let response = String::from_utf8_lossy(&buffer[..n]);

            Ok(response.to_string())
        } else {
            Err("No connection available".into())
        }
    }
}

# [async_trait::async_trait]
trait AsyncSubject {
    async fn request(&self, data: &str) -> String;
}

# [async_trait::async_trait]
impl AsyncSubject for RemoteProxy {
    async fn request(&self, data: &str) -> String {
        match self.send_request(data).await {
            Ok(response) => response,
            Err(e) => format!("Error: {}", e),
        }
    }
}

// 本地回退实现
impl Subject for RemoteProxy {
    fn request(&self, data: &str) -> String {
        // 同步版本使用本地实现作为回退
        if self.real_subject.is_none() {
            let mut proxy = RemoteProxy {
                real_subject: Some(Arc::new(RealSubject::new())),
                server_address: self.server_address.clone(),
                connection: Arc::clone(&self.connection),
            };
            proxy.real_subject.as_ref().unwrap().request(data)
        } else {
            self.real_subject.as_ref().unwrap().request(data)
        }
    }
}
```

## 6. 应用场景

### 6.1 图片加载代理

```rust
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

// 图片接口
trait Image {
    fn display(&self);
    fn get_size(&self) -> (u32, u32);
}

// 真实图片
struct RealImage {
    filename: String,
    width: u32,
    height: u32,
    loaded: bool,
}

impl RealImage {
    fn new(filename: String) -> Self {
        println!("Loading image: {}", filename);
        // 模拟图片加载
        RealImage {
            filename,
            width: 1920,
            height: 1080,
            loaded: true,
        }
    }
}

impl Image for RealImage {
    fn display(&self) {
        println!("Displaying image: {} ({}x{})", self.filename, self.width, self.height);
    }

    fn get_size(&self) -> (u32, u32) {
        (self.width, self.height)
    }
}

// 图片代理
struct ImageProxy {
    filename: String,
    real_image: Arc<Mutex<Option<RealImage>>>,
}

impl ImageProxy {
    fn new(filename: String) -> Self {
        ImageProxy {
            filename,
            real_image: Arc::new(Mutex::new(None)),
        }
    }

    fn load_image(&self) {
        let mut guard = self.real_image.lock().unwrap();
        if guard.is_none() {
            *guard = Some(RealImage::new(self.filename.clone()));
        }
    }
}

impl Image for ImageProxy {
    fn display(&self) {
        self.load_image();
        if let Some(ref image) = *self.real_image.lock().unwrap() {
            image.display();
        }
    }

    fn get_size(&self) -> (u32, u32) {
        self.load_image();
        if let Some(ref image) = *self.real_image.lock().unwrap() {
            image.get_size()
        } else {
            (0, 0)
        }
    }
}

// 图片查看器
struct ImageViewer {
    images: Vec<Arc<dyn Image>>,
}

impl ImageViewer {
    fn new() -> Self {
        ImageViewer {
            images: Vec::new(),
        }
    }

    fn add_image(&mut self, image: Arc<dyn Image>) {
        self.images.push(image);
    }

    fn display_all(&self) {
        for image in &self.images {
            image.display();
        }
    }
}
```

### 6.2 数据库连接代理

```rust
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;
use std::time::{Duration, Instant};

// 数据库连接
struct DatabaseConnection {
    id: String,
    created_at: Instant,
    last_used: Instant,
}

impl DatabaseConnection {
    fn new(id: String) -> Self {
        let now = Instant::now();
        DatabaseConnection {
            id,
            created_at: now,
            last_used: now,
        }
    }

    fn execute_query(&mut self, query: &str) -> String {
        self.last_used = Instant::now();
        println!("Connection {} executing: {}", self.id, query);
        format!("Result from connection {}: {}", self.id, query)
    }

    fn is_expired(&self, max_age: Duration) -> bool {
        self.created_at.elapsed() > max_age
    }

    fn is_idle(&self, idle_timeout: Duration) -> bool {
        self.last_used.elapsed() > idle_timeout
    }
}

// 连接池代理
struct ConnectionPoolProxy {
    pool: Arc<Mutex<VecDeque<DatabaseConnection>>>,
    max_connections: usize,
    max_age: Duration,
    idle_timeout: Duration,
}

impl ConnectionPoolProxy {
    fn new(max_connections: usize, max_age: Duration, idle_timeout: Duration) -> Self {
        ConnectionPoolProxy {
            pool: Arc::new(Mutex::new(VecDeque::new())),
            max_connections,
            max_age,
            idle_timeout,
        }
    }

    fn get_connection(&self) -> Option<DatabaseConnection> {
        let mut pool = self.pool.lock().unwrap();

        // 清理过期和空闲连接
        pool.retain(|conn| !conn.is_expired(self.max_age) && !conn.is_idle(self.idle_timeout));

        pool.pop_front()
    }

    fn return_connection(&self, mut connection: DatabaseConnection) {
        let mut pool = self.pool.lock().unwrap();

        if pool.len() < self.max_connections {
            pool.push_back(connection);
        }
    }

    fn execute_query(&self, query: &str) -> String {
        if let Some(mut connection) = self.get_connection() {
            let result = connection.execute_query(query);
            self.return_connection(connection);
            result
        } else {
            // 创建新连接
            let mut new_connection = DatabaseConnection::new(format!("conn_{}", uuid::Uuid::new_v4()));
            let result = new_connection.execute_query(query);
            self.return_connection(new_connection);
            result
        }
    }
}
```

### 6.3 安全代理

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

// 用户权限
# [derive(Clone, Debug)]
struct UserPermissions {
    user_id: String,
    roles: Vec<String>,
    permissions: Vec<String>,
}

impl UserPermissions {
    fn new(user_id: String, roles: Vec<String>, permissions: Vec<String>) -> Self {
        UserPermissions {
            user_id,
            roles,
            permissions,
        }
    }

    fn has_permission(&self, permission: &str) -> bool {
        self.permissions.contains(&permission.to_string())
    }

    fn has_role(&self, role: &str) -> bool {
        self.roles.contains(&role.to_string())
    }
}

// 安全服务
struct SecurityService {
    real_service: Option<Arc<dyn Subject>>,
    user_permissions: Arc<RwLock<HashMap<String, UserPermissions>>>,
}

impl SecurityService {
    fn new() -> Self {
        let mut permissions = HashMap::new();
        permissions.insert(
            "admin".to_string(),
            UserPermissions::new(
                "admin".to_string(),
                vec!["admin".to_string()],
                vec!["read".to_string(), "write".to_string(), "delete".to_string()],
            ),
        );
        permissions.insert(
            "user".to_string(),
            UserPermissions::new(
                "user".to_string(),
                vec!["user".to_string()],
                vec!["read".to_string()],
            ),
        );
        permissions.insert(
            "guest".to_string(),
            UserPermissions::new(
                "guest".to_string(),
                vec!["guest".to_string()],
                vec![],
            ),
        );

        SecurityService {
            real_service: None,
            user_permissions: Arc::new(RwLock::new(permissions)),
        }
    }

    fn check_permission(&self, user_id: &str, operation: &str) -> bool {
        let permissions = self.user_permissions.read().unwrap();
        if let Some(user_perm) = permissions.get(user_id) {
            user_perm.has_permission(operation)
        } else {
            false
        }
    }

    fn lazy_init(&mut self) {
        if self.real_service.is_none() {
            self.real_service = Some(Arc::new(RealSubject::new()));
        }
    }
}

impl Subject for SecurityService {
    fn request(&self, data: &str) -> String {
        // 解析请求: "user_id:operation:data"
        let parts: Vec<&str> = data.split(':').collect();
        if parts.len() != 3 {
            return "Invalid request format".to_string();
        }

        let user_id = parts[0];
        let operation = parts[1];
        let actual_data = parts[2];

        // 检查权限
        if !self.check_permission(user_id, operation) {
            return format!("Access denied for user '{}' to operation '{}'", user_id, operation);
        }

        // 延迟初始化
        let mut service = SecurityService {
            real_service: self.real_service.clone(),
            user_permissions: Arc::clone(&self.user_permissions),
        };
        service.lazy_init();

        // 委托给真实服务
        if let Some(ref real_service) = service.real_service {
            real_service.request(actual_data)
        } else {
            "Error: RealService not initialized".to_string()
        }
    }
}
```

## 7. 变体模式

### 7.1 智能引用代理

```rust
use std::sync::{Arc, Mutex};

// 智能引用代理
struct SmartReferenceProxy {
    real_subject: Arc<Mutex<Option<Arc<RealSubject>>>>,
    reference_count: Arc<Mutex<usize>>,
    max_references: usize,
}

impl SmartReferenceProxy {
    fn new(max_references: usize) -> Self {
        SmartReferenceProxy {
            real_subject: Arc::new(Mutex::new(None)),
            reference_count: Arc::new(Mutex::new(0)),
            max_references,
        }
    }

    fn acquire_reference(&self) -> bool {
        let mut count = self.reference_count.lock().unwrap();
        if *count < self.max_references {
            *count += 1;
            true
        } else {
            false
        }
    }

    fn release_reference(&self) {
        let mut count = self.reference_count.lock().unwrap();
        if *count > 0 {
            *count -= 1;
        }
    }

    fn get_reference_count(&self) -> usize {
        *self.reference_count.lock().unwrap()
    }
}

impl Subject for SmartReferenceProxy {
    fn request(&self, data: &str) -> String {
        if !self.acquire_reference() {
            return "Too many references".to_string();
        }

        // 延迟初始化
        {
            let mut subject = self.real_subject.lock().unwrap();
            if subject.is_none() {
                *subject = Some(Arc::new(RealSubject::new()));
            }
        }

        // 执行请求
        let result = {
            let subject = self.real_subject.lock().unwrap();
            if let Some(ref real_subject) = *subject {
                real_subject.request(data)
            } else {
                "Error: RealSubject not initialized".to_string()
            }
        };

        self.release_reference();
        result
    }
}
```

### 7.2 同步代理

```rust
use std::sync::{Arc, Mutex, Condvar};

// 同步代理
struct SynchronizationProxy {
    real_subject: Arc<Mutex<Option<Arc<RealSubject>>>>,
    busy: Arc<(Mutex<bool>, Condvar)>,
}

impl SynchronizationProxy {
    fn new() -> Self {
        SynchronizationProxy {
            real_subject: Arc::new(Mutex::new(None)),
            busy: Arc::new((Mutex::new(false), Condvar::new())),
        }
    }

    fn acquire_lock(&self) {
        let (lock, cvar) = &*self.busy;
        let mut busy = lock.lock().unwrap();
        while *busy {
            busy = cvar.wait(busy).unwrap();
        }
        *busy = true;
    }

    fn release_lock(&self) {
        let (lock, cvar) = &*self.busy;
        let mut busy = lock.lock().unwrap();
        *busy = false;
        cvar.notify_one();
    }
}

impl Subject for SynchronizationProxy {
    fn request(&self, data: &str) -> String {
        self.acquire_lock();

        // 延迟初始化
        {
            let mut subject = self.real_subject.lock().unwrap();
            if subject.is_none() {
                *subject = Some(Arc::new(RealSubject::new()));
            }
        }

        // 执行请求
        let result = {
            let subject = self.real_subject.lock().unwrap();
            if let Some(ref real_subject) = *subject {
                real_subject.request(data)
            } else {
                "Error: RealSubject not initialized".to_string()
            }
        };

        self.release_lock();
        result
    }
}
```

### 7.3 防火墙代理

```rust
use std::collections::HashSet;
use std::sync::{Arc, RwLock};

// 防火墙代理
struct FirewallProxy {
    real_subject: Arc<Mutex<Option<Arc<RealSubject>>>>,
    blacklist: Arc<RwLock<HashSet<String>>>,
    whitelist: Arc<RwLock<HashSet<String>>>,
    request_count: Arc<RwLock<HashMap<String, u64>>>,
    rate_limit: u64,
}

impl FirewallProxy {
    fn new(rate_limit: u64) -> Self {
        let mut blacklist = HashSet::new();
        blacklist.insert("malicious_ip".to_string());
        blacklist.insert("blocked_user".to_string());

        let mut whitelist = HashSet::new();
        whitelist.insert("trusted_ip".to_string());
        whitelist.insert("admin_user".to_string());

        FirewallProxy {
            real_subject: Arc::new(Mutex::new(None)),
            blacklist: Arc::new(RwLock::new(blacklist)),
            whitelist: Arc::new(RwLock::new(whitelist)),
            request_count: Arc::new(RwLock::new(HashMap::new())),
            rate_limit,
        }
    }

    fn is_blocked(&self, client_id: &str) -> bool {
        let blacklist = self.blacklist.read().unwrap();
        blacklist.contains(client_id)
    }

    fn is_whitelisted(&self, client_id: &str) -> bool {
        let whitelist = self.whitelist.read().unwrap();
        whitelist.contains(client_id)
    }

    fn check_rate_limit(&self, client_id: &str) -> bool {
        let mut count = self.request_count.write().unwrap();
        let current_count = count.entry(client_id.to_string()).or_insert(0);
        *current_count += 1;
        *current_count <= self.rate_limit
    }

    fn reset_rate_limit(&self, client_id: &str) {
        let mut count = self.request_count.write().unwrap();
        count.remove(client_id);
    }
}

impl Subject for FirewallProxy {
    fn request(&self, data: &str) -> String {
        // 解析客户端ID
        let parts: Vec<&str> = data.split(':').collect();
        if parts.len() < 2 {
            return "Invalid request format".to_string();
        }

        let client_id = parts[0];
        let actual_data = parts[1..].join(":");

        // 检查黑名单
        if self.is_blocked(client_id) {
            return format!("Access denied: {} is blacklisted", client_id);
        }

        // 检查白名单（跳过速率限制）
        if !self.is_whitelisted(client_id) {
            // 检查速率限制
            if !self.check_rate_limit(client_id) {
                return format!("Rate limit exceeded for client: {}", client_id);
            }
        }

        // 延迟初始化
        {
            let mut subject = self.real_subject.lock().unwrap();
            if subject.is_none() {
                *subject = Some(Arc::new(RealSubject::new()));
            }
        }

        // 执行请求
        let result = {
            let subject = self.real_subject.lock().unwrap();
            if let Some(ref real_subject) = *subject {
                real_subject.request(&actual_data)
            } else {
                "Error: RealSubject not initialized".to_string()
            }
        };

        result
    }
}
```

## 8. 性能分析

### 8.1 代理开销分析

**定理8.1 (代理开销)**
代理模式的性能开销为：

$$\text{Overhead}_{proxy} = \text{AccessControl} + \text{Caching} + \text{Delegation}$$

其中：

- $\text{AccessControl}$ 是访问控制的开销
- $\text{Caching}$ 是缓存管理的开销
- $\text{Delegation}$ 是委托操作的开销

### 8.2 内存使用分析

**定理8.2 (内存使用)**
代理模式的内存使用为：

$$\text{MemoryUsage}_{proxy} = \text{MemoryUsage}_{real} + \text{MemoryUsage}_{proxy\_overhead}$$

其中 $\text{MemoryUsage}_{proxy\_overhead}$ 是代理本身的内存开销。

### 8.3 延迟分析

**定理8.3 (延迟分析)**
代理模式的延迟为：

$$\text{Latency}_{proxy} = \text{Latency}_{real} + \text{Latency}_{proxy\_processing}$$

其中 $\text{Latency}_{proxy\_processing}$ 是代理处理的开销。

## 9. 总结

### 9.1 模式优势

1. **访问控制**：提供细粒度的访问控制机制
2. **延迟加载**：支持按需加载大对象
3. **缓存优化**：通过缓存提高性能
4. **远程访问**：支持分布式系统中的远程对象访问
5. **安全增强**：提供额外的安全层

### 9.2 模式限制

1. **性能开销**：代理层增加了一定的性能开销
2. **复杂性增加**：需要管理代理和真实主题的关系
3. **调试困难**：代理层可能使调试变得复杂

### 9.3 最佳实践

1. **接口一致性**：确保代理和真实主题实现相同的接口
2. **透明性**：客户端应该能够透明地使用代理
3. **性能优化**：根据具体需求选择合适的代理类型
4. **错误处理**：提供适当的错误处理机制

### 9.4 形式化验证

通过形式化定义和数学证明，我们建立了代理模式的完整理论体系：

1. **代理正确性**：确保代理行为的正确性
2. **访问控制安全性**：提供访问控制的安全保证
3. **延迟加载正确性**：保证延迟加载的正确性
4. **性能保证**：建立性能的数学模型

这个形式化框架为代理模式的设计、实现和验证提供了坚实的理论基础。
