# Proxy Pattern in Rust

> **设计模式**: 结构型模式
> **难度**: 🟡 中等
> **应用场景**: 访问控制、延迟加载、缓存

---

## 概念

代理模式为其他对象提供一种代理以控制对这个对象的访问。

---

## 代理类型

### 1. 虚拟代理 (延迟加载)

```rust
use std::sync::OnceLock;

pub trait Image {
    fn display(&self);
    fn width(&self) -> u32;
    fn height(&self) -> u32;
}

// 真实对象
pub struct RealImage {
    filename: String,
    data: Vec<u8>,
}

impl RealImage {
    fn new(filename: &str) -> Self {
        println!("Loading image from disk: {}", filename);
        Self {
            filename: filename.to_string(),
            data: vec![0; 1024 * 1024], // 模拟大数据
        }
    }
}

impl Image for RealImage {
    fn display(&self) {
        println!("Displaying: {}", self.filename);
    }
    fn width(&self) -> u32 { 1920 }
    fn height(&self) -> u32 { 1080 }
}

// 虚拟代理
pub struct ProxyImage {
    filename: String,
    real_image: OnceLock<RealImage>,
}

impl ProxyImage {
    pub fn new(filename: &str) -> Self {
        Self {
            filename: filename.to_string(),
            real_image: OnceLock::new(),
        }
    }

    fn get_real(&self) -> &RealImage {
        self.real_image.get_or_init(|| {
            RealImage::new(&self.filename)
        })
    }
}

impl Image for ProxyImage {
    fn display(&self) {
        self.get_real().display();
    }
    fn width(&self) -> u32 { 1920 } // 可以从元数据获取
    fn height(&self) -> u32 { 1080 }
}
```

### 2. 保护代理 (访问控制)

```rust
pub trait Document {
    fn read(&self) -> String;
    fn write(&mut self, content: &str);
}

pub struct RealDocument {
    content: String,
}

impl RealDocument {
    pub fn new(content: &str) -> Self {
        Self {
            content: content.to_string(),
        }
    }
}

impl Document for RealDocument {
    fn read(&self) -> String {
        self.content.clone()
    }

    fn write(&mut self, content: &str) {
        self.content = content.to_string();
    }
}

pub enum Role {
    Reader,
    Writer,
    Admin,
}

pub struct ProtectedDocument {
    document: RealDocument,
    user_role: Role,
}

impl ProtectedDocument {
    pub fn new(content: &str, user_role: Role) -> Self {
        Self {
            document: RealDocument::new(content),
            user_role,
        }
    }
}

impl Document for ProtectedDocument {
    fn read(&self) -> String {
        match self.user_role {
            Role::Reader | Role::Writer | Role::Admin => self.document.read(),
        }
    }

    fn write(&mut self, content: &str) {
        match self.user_role {
            Role::Writer | Role::Admin => self.document.write(content),
            Role::Reader => println!("Access denied: Reader cannot write"),
        }
    }
}
```

### 3. 智能引用 (引用计数)

```rust
use std::ops::{Deref, DerefMut};
use std::sync::Arc;

pub struct SmartPointer<T> {
    data: Arc<T>,
    access_count: std::cell::Cell<u64>,
}

impl<T> SmartPointer<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(data),
            access_count: std::cell::Cell::new(0),
        }
    }

    pub fn access_count(&self) -> u64 {
        self.access_count.get()
    }
}

impl<T> Deref for SmartPointer<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.access_count.set(self.access_count.get() + 1);
        &self.data
    }
}
```

---

## 形式化定义

```
Proxy<T> ≈ T (在接口上)

但满足额外约束:
  - Virtual: 延迟初始化
  - Protection: 访问控制 predicate
  - Smart: 附加行为 (计数、日志等)
```
