# Type-Driven Correctness：类型驱动的正确性

> **最后更新日期**: 2026-04-24  
> **难度级别**: 高级  
> **前置知识**: 泛型、Trait、PhantomData、所有权系统

---

## 1. 核心思想

**Type-Driven Correctness**（类型驱动的正确性）是一种利用 Rust 类型系统将程序约束编码到类型中的编程范式。核心思想：

> **"如果程序能编译，那么某些错误在运行时就不可能发生。"**

通过在类型层面编码状态和约束，我们可以在编译时排除大量逻辑错误，减少运行时检查和测试负担。

---

## 2. Type-State 模式

### 2.1 什么是 Type-State？

Type-State 模式将对象的**运行时状态**提升为**编译时类型**，使得非法状态转换在编译时被拒绝。

### 2.2 经典示例：文件状态机

```rust
use std::marker::PhantomData;

// === 状态标签 (零大小类型) ===
#[derive(Debug)]
pub struct Closed;
#[derive(Debug)]
pub struct Open;
#[derive(Debug)]
pub struct Reading;

// === 文件句柄，状态由类型参数编码 ===
pub struct FileHandle<State> {
    path: String,
    // PhantomData 用于在类型层面携带状态信息，不占内存
    _state: PhantomData<State>,
}

impl FileHandle<Closed> {
    pub fn new(path: impl Into<String>) -> Self {
        Self {
            path: path.into(),
            _state: PhantomData,
        }
    }

    /// 打开文件：Closed → Open
    pub fn open(self) -> FileHandle<Open> {
        println!("打开文件: {}", self.path);
        FileHandle {
            path: self.path,
            _state: PhantomData,
        }
    }
}

impl FileHandle<Open> {
    /// 开始读取：Open → Reading
    pub fn start_read(self) -> FileHandle<Reading> {
        println!("开始读取...");
        FileHandle {
            path: self.path,
            _state: PhantomData,
        }
    }

    /// 关闭文件：Open → Closed
    pub fn close(self) -> FileHandle<Closed> {
        println!("关闭文件");
        FileHandle {
            path: self.path,
            _state: PhantomData,
        }
    }
}

impl FileHandle<Reading> {
    /// 读取数据 (仅在 Reading 状态下可用)
    pub fn read_chunk(&self) -> Vec<u8> {
        println!("读取数据块...");
        vec![1, 2, 3] // 模拟数据
    }

    /// 完成读取：Reading → Open
    pub fn finish_read(self) -> FileHandle<Open> {
        println!("完成读取");
        FileHandle {
            path: self.path,
            _state: PhantomData,
        }
    }
}

/// 使用示例
pub fn demo_type_state() {
    let file = FileHandle::new("data.txt");
    let file = file.open();
    let file = file.start_read();
    let _data = file.read_chunk();
    let file = file.finish_read();
    let _file = file.close();

    // 以下代码无法编译 (编译时状态机检查):
    // let file = FileHandle::new("data.txt");
    // file.read_chunk(); // ❌ 错误: FileHandle<Closed> 没有 read_chunk 方法
}
```

### 2.3 实际应用场景：HTTP 请求构建器

```rust
use std::marker::PhantomData;

// 请求构建阶段
#[derive(Debug)]
pub struct NoUrl;
#[derive(Debug)]
pub struct HasUrl;
#[derive(Debug)]
pub struct Built;

pub struct RequestBuilder<State> {
    url: Option<String>,
    method: String,
    headers: Vec<(String, String)>,
    _state: PhantomData<State>,
}

impl RequestBuilder<NoUrl> {
    pub fn new() -> Self {
        Self {
            url: None,
            method: "GET".to_string(),
            headers: Vec::new(),
            _state: PhantomData,
        }
    }

    pub fn url(self, url: impl Into<String>) -> RequestBuilder<HasUrl> {
        RequestBuilder {
            url: Some(url.into()),
            method: self.method,
            headers: self.headers,
            _state: PhantomData,
        }
    }
}

impl RequestBuilder<HasUrl> {
    pub fn method(mut self, method: impl Into<String>) -> Self {
        self.method = method.into();
        self
    }

    pub fn header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.push((key.into(), value.into()));
        self
    }

    pub fn build(self) -> RequestBuilder<Built> {
        RequestBuilder {
            url: self.url,
            method: self.method,
            headers: self.headers,
            _state: PhantomData,
        }
    }
}

impl RequestBuilder<Built> {
    pub fn send(&self) {
        println!(
            "发送 {} 请求到 {}",
            self.method,
            self.url.as_ref().unwrap()
        );
    }
}

pub fn demo_request_builder() {
    // ✅ 正确的构建流程
    RequestBuilder::new()
        .url("https://api.example.com")
        .method("POST")
        .header("Content-Type", "application/json")
        .build()
        .send();

    // ❌ 编译错误: 没有 url 不能 build
    // RequestBuilder::new().build().send();
}
```

---

## 3. Phantom Types（幻影类型）

### 3.1 概念

Phantom Types 是**仅用于类型参数、不承载数据**的类型。它们与 `PhantomData` 结合使用，在编译时编码额外的类型约束。

### 3.2 示例：单位安全的物理计算

```rust
use std::marker::PhantomData;
use std::ops::{Add, Mul};

// === 单位标签 ===
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Meter;
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Second;
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Kilogram;

// === 复合单位: Meter/Second ===
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Per<N, D>(PhantomData<(N, D)>);

// === 带单位的数值 ===
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Quantity<T, Unit>(pub T, pub PhantomData<Unit>);

impl<T: Copy, U> Quantity<T, U> {
    pub fn new(val: T) -> Self {
        Quantity(val, PhantomData)
    }

    pub fn value(&self) -> T {
        self.0
    }
}

// 相同单位可以相加
impl<T: Add<Output = T>, U> Add for Quantity<T, U> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Quantity::new(self.0 + rhs.0)
    }
}

// 乘法: Meter * Meter = Meter² (简化演示，仅传递第一个单位)
impl<T: Mul<Output = T>, U> Mul for Quantity<T, U> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Quantity::new(self.0 * rhs.0)
    }
}

// 类型别名: 提高可读性
pub type Length = Quantity<f64, Meter>;
pub type Time = Quantity<f64, Second>;
pub type Mass = Quantity<f64, Kilogram>;
pub type Velocity = Quantity<f64, Per<Meter, Second>>;

/// 计算速度: distance / time
pub fn velocity(distance: Length, time: Time) -> Velocity {
    Quantity::new(distance.value() / time.value())
}

pub fn demo_phantom_types() {
    let d = Length::new(100.0);
    let t = Time::new(10.0);
    let m = Mass::new(5.0);

    let v = velocity(d, t);
    println!("速度: {:?}", v);

    // 以下代码在编译时被阻止:
    // let wrong = velocity(d, m); // ❌ Mass 不是 Time
    // let sum = d + t;            // ❌ Length 不能和 Time 相加
}
```

---

## 4. Capability Tokens（能力令牌）

### 4.1 什么是 Capability？

Capability 安全模型是一种访问控制范式：**持有某个类型的值，就证明了拥有对应的权限**。

### 4.2 示例：权限分级文件系统访问

```rust
use std::marker::PhantomData;

// === 权限标签 ===
#[derive(Debug)]
pub struct Read;
#[derive(Debug)]
pub struct Write;
#[derive(Debug)]
pub struct Admin;

// 权限组合: Read + Write
#[derive(Debug)]
pub struct ReadWrite;

/// 能力令牌: 持有它即拥有对应权限
pub struct Capability<Permission>(PhantomData<Permission>);

impl<P> Capability<P> {
    fn new() -> Self {
        Capability(PhantomData)
    }
}

/// 文件系统操作，需要对应的能力令牌
pub struct SecureFS;

impl SecureFS {
    pub fn read_file(&self, _cap: &Capability<Read>, path: &str) -> String {
        println!("[Read] 读取文件: {}", path);
        format!("content of {}", path)
    }

    pub fn write_file(&self, _cap: &Capability<Write>, path: &str, content: &str) {
        println!("[Write] 写入文件: {} <= {}", path, content);
    }

    pub fn delete_file(&self, _cap: &Capability<Admin>, path: &str) {
        println!("[Admin] 删除文件: {}", path);
    }
}

/// 权限管理器
pub struct AuthManager;

impl AuthManager {
    /// 游客只能获取读权限
    pub fn guest_login(&self) -> Capability<Read> {
        Capability::new()
    }

    /// 用户可以获取读写权限
    pub fn user_login(&self) -> (Capability<Read>, Capability<Write>) {
        (Capability::new(), Capability::new())
    }

    /// 管理员获取所有权限
    pub fn admin_login(&self) -> (Capability<Read>, Capability<Write>, Capability<Admin>) {
        (Capability::new(), Capability::new(), Capability::new())
    }
}

pub fn demo_capability_tokens() {
    let fs = SecureFS;
    let auth = AuthManager;

    // 游客只能读
    let read_cap = auth.guest_login();
    let _content = fs.read_file(&read_cap, "data.txt");
    // fs.write_file(&read_cap, "data.txt", "x"); // ❌ Capability<Read> ≠ Capability<Write>

    // 用户可以读写
    let (r, w) = auth.user_login();
    fs.read_file(&r, "data.txt");
    fs.write_file(&w, "data.txt", "new content");
    // fs.delete_file(&w, "data.txt"); // ❌ 需要 Admin 权限

    // 管理员可以删除
    let (r, w, a) = auth.admin_login();
    fs.read_file(&r, "data.txt");
    fs.write_file(&w, "data.txt", "admin data");
    fs.delete_file(&a, "data.txt"); // ✅ 成功
}
```

### 4.3 运行时零成本

能力令牌模式的关键优势：

```rust
use std::mem::size_of;

// Capability 只有 PhantomData，零大小
assert_eq!(size_of::<Capability<Read>>(), 0);

// 函数参数传递零开销
// fs.read_file(&cap, path) 在运行时和直接调用无区别
```

---

## 5. 综合示例：类型安全的资源生命周期管理

```rust
use std::marker::PhantomData;

// === 资源生命周期状态 ===
#[derive(Debug)]
pub struct Uninitialized;
#[derive(Debug)]
pub struct Initialized;
#[derive(Debug)]
pub struct Running;
#[derive(Debug)]
pub struct Stopped;

/// 类型安全的资源管理器
pub struct ResourceManager<State> {
    name: String,
    config: Option<String>,
    _state: PhantomData<State>,
}

impl ResourceManager<Uninitialized> {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            config: None,
            _state: PhantomData,
        }
    }

    pub fn configure(self, config: impl Into<String>) -> ResourceManager<Initialized> {
        ResourceManager {
            name: self.name,
            config: Some(config.into()),
            _state: PhantomData,
        }
    }
}

impl ResourceManager<Initialized> {
    pub fn start(self) -> Result<ResourceManager<Running>, String> {
        println!("[{}] 启动资源", self.name);
        Ok(ResourceManager {
            name: self.name,
            config: self.config,
            _state: PhantomData,
        })
    }
}

impl ResourceManager<Running> {
    pub fn do_work(&self) -> String {
        format!("[{}] 处理中: {:?}", self.name, self.config)
    }

    pub fn stop(self) -> ResourceManager<Stopped> {
        println!("[{}] 停止资源", self.name);
        ResourceManager {
            name: self.name,
            config: self.config,
            _state: PhantomData,
        }
    }
}

impl ResourceManager<Stopped> {
    pub fn restart(self) -> Result<ResourceManager<Running>, String> {
        println!("[{}] 重启资源", self.name);
        Ok(ResourceManager {
            name: self.name,
            config: self.config,
            _state: PhantomData,
        })
    }

    pub fn reconfigure(self, config: impl Into<String>) -> ResourceManager<Initialized> {
        ResourceManager {
            name: self.name,
            config: Some(config.into()),
            _state: PhantomData,
        }
    }
}

pub fn demo_lifecycle_management() {
    let result: Result<_, String> = (|| {
        let res = ResourceManager::new("Database");
        let res = res.configure("host=localhost;port=5432");
        let res = res.start()?;
        println!("{}", res.do_work());
        let res = res.stop();
        let res = res.restart()?;
        println!("{}", res.do_work());
        let res = res.stop();
        Ok(res)
    })();

    assert!(result.is_ok());
}
```

---

## 6. 模式对比与选择指南

| 模式 | 核心机制 | 适用场景 | 运行时成本 |
|------|---------|---------|-----------|
| **Type-State** | 状态 → 类型参数 | 状态机、工作流 | 零 |
| **Phantom Types** | 幽灵类型标签 | 单位检查、领域建模 | 零 |
| **Capability Tokens** | 能力 → 类型持有 | 权限控制、访问管理 | 零 |

### 何时使用？

- **使用 Type-State**: 当对象有明确的生命周期阶段，且某些操作只在特定阶段合法时
- **使用 Phantom Types**: 当需要在类型层面编码额外的语义信息（单位、格式、协议版本）时
- **使用 Capability Tokens**: 当需要细粒度的访问控制，且权限应在编译时验证时

---

## 7. 注意事项

1. **API 复杂度**: 类型驱动的正确性会增加 API 的表面积（每个状态一个 impl 块）
2. **文档必要性**: 必须清楚说明类型状态转换规则
3. **错误信息**: 编译错误可能较晦涩，需要设计友好的类型名
4. **过度设计**: 不是所有状态都需要提升到类型层面

---

## 8. 参考文献

1. **Aldrich, J.** *"Typestate-Oriented Programming"*. Onward! 2009.  
   (Type-State 模式的奠基论文)

2. **Clarke, D., & Drossopoulou, S.** *"Ownership, Encapsulation and the Disjointness of Type and Effect"*. OOPSLA 2002.  
   (Capability 安全模型的类型系统基础)

3. **Rust RFC 0738: Variance**.  
   <https://rust-lang.github.io/rfcs/0738-variance.html>  
   (PhantomData 与变型的关系)

4. **Rust By Example: Phantom Types**.  
   <https://doc.rust-lang.org/rust-by-example/generics/phantom.html>

5. **The Rust Programming Language (TRPL) Chapter 19**. "Advanced Traits".  
   (PhantomData 和高级泛型模式)

---

> 📌 **复查记录**
> - 2026-04-24: 初始创建
> - 下次复查: 随 Rust 版本更新时复查
