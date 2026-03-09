# 理论到设计模式桥梁文档

> 从形式化理论到 Rust 设计模式的映射

---

## 引言：为什么需要理论指导模式？

**问题**: 面对设计问题时，如何选择正确的模式？

**答案**: 理解模式背后的理论约束，让理论指导设计决策。

---

## 一、所有权约束与设计模式

### 1.1 线性逻辑 → RAII 模式

**理论基础**: 线性逻辑要求资源恰好使用一次

**模式**: RAII (Resource Acquisition Is Initialization)

```rust
// 理论对应: 资源在构造时获得，在析构时释放
// 对应线性逻辑: A ⊸ B (转移所有权)

pub struct FileHandle {
    fd: RawFd,
}

impl FileHandle {
    // 获得资源
    pub fn open(path: &str) -> io::Result<Self> {
        let fd = syscall_open(path)?;
        Ok(Self { fd })
    }
}

impl Drop for FileHandle {
    // 释放资源 - 对应线性逻辑的 "使用"
    fn drop(&mut self) {
        syscall_close(self.fd);
    }
}

// 使用: 资源转移保证安全
fn use_file() {
    let file = FileHandle::open("data.txt").unwrap();
    process(&file);
    // file 在这里 drop，资源被正确释放
}
```

**理论约束**:

- 资源必须被使用（不能泄露）
- 资源只能被使用一次（不能重复释放）

### 1.2 仿射类型 → Builder 模式

**理论基础**: 仿射类型允许使用 0 次或 1 次

**模式**: Builder 模式（分阶段构造）

```rust
// 理论对应: 部分构造的状态可以丢弃（0次使用）
// 或者完成构造后使用（1次使用）

pub struct ConfigBuilder {
    host: Option<String>,
    port: Option<u16>,
}

impl ConfigBuilder {
    pub fn new() -> Self {
        Self {
            host: None,
            port: None,
        }
    }

    // 每个方法返回 Self，允许链式调用
    // 对应: 仿射类型的 "部分应用"
    pub fn host(mut self, host: impl Into<String>) -> Self {
        self.host = Some(host.into());
        self  // 转移所有权到新的 builder
    }

    pub fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }

    // 最终消费 builder，产生 Config
    // 对应: 仿射类型的 "使用"
    pub fn build(self) -> Result<Config, BuildError> {
        Ok(Config {
            host: self.host.ok_or(BuildError::MissingHost)?,
            port: self.port.unwrap_or(8080),
        })
    }
}

// 使用: 可以中途放弃（0次使用）或完成（1次使用）
fn example() {
    // 中途放弃 - 合法（仿射类型允许 0 次使用）
    let _ = ConfigBuilder::new().host("localhost");

    // 完成构造 - 合法（仿射类型允许 1 次使用）
    let config = ConfigBuilder::new()
        .host("localhost")
        .port(3000)
        .build()?;
}
```

### 1.3 区域类型 → 类型状态模式

**理论基础**: 区域类型限制值的有效期

**模式**: 类型状态（编译期状态机）

```rust
// 理论对应: 不同类型状态在不同"区域"有效

pub struct Disconnected;
pub struct Connecting;
pub struct Connected;
pub struct Closed;

pub struct Connection<State> {
    state: State,
    // ...
}

// 在 Disconnected 区域，只能连接
impl Connection<Disconnected> {
    pub fn connect(self) -> Connection<Connecting> {
        // 转移到一个新的"区域"
        Connection { state: Connecting }
    }
}

// 在 Connecting 区域，可以完成连接
impl Connection<Connecting> {
    pub fn finalize(self) -> Result<Connection<Connected>, Connection<Disconnected>> {
        // 成功或失败，转移到不同区域
        if try_connect() {
            Ok(Connection { state: Connected })
        } else {
            Err(Connection { state: Disconnected })
        }
    }
}

// 在 Connected 区域，可以发送数据
impl Connection<Connected> {
    pub fn send(&self, data: &[u8]) -> Result<(), Error>;

    pub fn close(self) -> Connection<Closed> {
        Connection { state: Closed }
    }
}

// Closed 区域没有方法 - 无法使用
```

---

## 二、借用约束与设计模式

### 2.1 借用规则 → 访问者模式

**理论基础**: 不能同时有可变和不可变借用

**模式**: 访问者模式（分离遍历和修改）

```rust
// 问题: 遍历树时不能修改节点
// 解决: 先收集信息，再统一修改

pub struct Ast {
    nodes: Vec<Node>,
}

// 访问者: 只读遍历
pub trait Visitor {
    fn visit_node(&mut self, node: &Node);
}

// 收集信息的访问者
struct CollectVars {
    vars: Vec<String>,
}

impl Visitor for CollectVars {
    fn visit_node(&mut self, node: &Node) {
        if let Node::Var(name) = node {
            self.vars.push(name.clone());
        }
    }
}

// 修改节点: 在遍历完成后
impl Ast {
    pub fn transform<F>(&mut self, f: F)
    where
        F: Fn(&Node) -> Option<Node>,
    {
        // 借用规则允许: &mut self 独占访问
        for node in &mut self.nodes {
            if let Some(new_node) = f(node) {
                *node = new_node;
            }
        }
    }
}
```

### 2.2 内部可变性 → Newtype 模式

**理论基础**: 在不可变引用后隐藏可变性

**模式**: Newtype + 内部可变性

```rust
use std::cell::RefCell;

// 理论对应: &T 后隐藏 &mut T (通过运行时检查)

pub struct Counter(RefCell<u64>);

impl Counter {
    pub fn new() -> Self {
        Self(RefCell::new(0))
    }

    // &self 但内部可修改
    // 对应: 在共享借用后提供可变访问
    pub fn increment(&self) {
        *self.0.borrow_mut() += 1;
    }

    pub fn get(&self) -> u64 {
        *self.0.borrow()
    }
}

// 使用: 可以有多个 &Counter，但都能"修改"
fn example() {
    let counter = Counter::new();

    let r1 = &counter;
    let r2 = &counter;

    r1.increment();  // 通过 &Counter 修改！
    r2.increment();

    println!("{}", counter.get());  // 2
}
```

---

## 三、生命周期约束与设计模式

### 3.1 生命周期约束 → 零拷贝模式

**理论基础**: 引用的有效期不能超过被引用者

**模式**: 零拷贝解析

```rust
// 理论对应: 解析结果的生命周期 ≤ 输入数据的生命周期

pub struct Parser<'a> {
    input: &'a str,
    position: usize,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Self {
        Self { input, position: 0 }
    }

    // 返回的 &str 与 input 有相同生命周期
    // 对应: T^ρ → T^ρ (保持区域)
    pub fn parse_word(&mut self) -> Option<&'a str> {
        let start = self.position;
        while self.position < self.input.len()
              && !self.input[self.position..].starts_with(' ') {
            self.position += 1;
        }

        if start < self.position {
            Some(&self.input[start..self.position])
        } else {
            None
        }
    }
}

// 使用: 解析结果不能活得比输入长
fn example() {
    let data = String::from("hello world");
    let word: &str;

    {
        let parser = Parser::new(&data);
        word = parser.parse_word().unwrap();
        // parser 在这里 drop
    }

    println!("{}", word);  // ✓ OK: word 和 data 生命周期相同
}
```

### 3.2 'static 约束 → 单例模式

**理论基础**: 'static 表示整个程序生命周期

**模式**: 懒加载单例

```rust
use std::sync::OnceLock;

// 理论对应: T^static - 值在整个程序期间有效

pub struct Config {
    pub database_url: String,
    pub port: u16,
}

// 'static 单例
static CONFIG: OnceLock<Config> = OnceLock::new();

impl Config {
    pub fn global() -> &'static Config {
        CONFIG.get_or_init(|| {
            Config {
                database_url: std::env::var("DATABASE_URL").unwrap(),
                port: std::env::var("PORT").unwrap().parse().unwrap(),
            }
        })
    }
}

// 使用: 返回 'static 引用，可以在任何地方使用
fn anywhere_in_program() -> &'static str {
    &Config::global().database_url
}
```

---

## 四、Send/Sync 约束与并发模式

### 4.1 Send 约束 → 线程池模式

**理论基础**: Send 表示可以跨线程转移所有权

**模式**: 工作窃取线程池

```rust
use crossbeam::channel;
use std::thread;

// 理论对应: T: Send 保证可以安全转移

pub struct ThreadPool {
    workers: Vec<Worker>,
    sender: channel::Sender<Job>,
}

type Job = Box<dyn FnOnce() + Send>;  // Send 是必须的！

impl ThreadPool {
    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,  // Send 允许跨线程
    {
        self.sender.send(Box::new(f)).unwrap();
    }
}

struct Worker {
    thread: thread::JoinHandle<()>,
}

impl Worker {
    fn new(receiver: channel::Receiver<Job>) -> Self {
        let thread = thread::spawn(move || {
            // 接收任务 - 所有权从发送线程转移到工作线程
            // 对应: Send 保证转移安全
            while let Ok(job) = receiver.recv() {
                job();  // 执行
            }
        });

        Self { thread }
    }
}
```

### 4.2 Sync 约束 → 读写锁模式

**理论基础**: Sync 表示可以跨线程共享引用

**模式**: 读写锁

```rust
use std::sync::RwLock;

// 理论对应: T: Sync 表示 &T: Send
//          可以安全地跨线程共享引用

pub struct Cache<K, V> {
    data: RwLock<HashMap<K, V>>,
}

impl<K: Eq + Hash, V: Clone> Cache<K, V> {
    // 读: 多个线程可以同时 &Cache
    pub fn get(&self, key: &K) -> Option<V> {
        let data = self.data.read().unwrap();
        data.get(key).cloned()
    }

    // 写: 需要独占访问
    pub fn insert(&self, key: K, value: V) {
        let mut data = self.data.write().unwrap();
        data.insert(key, value);
    }
}

// 使用: Cache<K, V>: Sync 当 K, V: Sync
// 可以安全地在多个线程间共享 &Cache
```

---

## 五、模式选择决策树

```
需要管理资源生命周期?
├── 是 → 资源在构造时获得?
│         ├── 是 → RAII 模式
│         └── 否 → 考虑其他模式
│
需要分阶段构造?
├── 是 → Builder 模式
│
需要编译期状态检查?
├── 是 → 类型状态模式
│
需要在共享引用后修改?
├── 是 → 内部可变性 + Newtype 模式
│
需要避免拷贝?
├── 是 → 零拷贝 + 生命周期标注
│
需要跨线程共享?
├── 是 → 检查 Send/Sync
│         ├── 需要转移 → Send
│         └── 需要共享 → Sync + Arc/Mutex
│
需要单例?
├── 是 → 'static + OnceLock
```

---

## 六、模式组合

### 6.1 RAII + 类型状态

```rust
pub struct Connection<State> {
    fd: RawFd,
    state: PhantomData<State>,
}

impl Connection<Disconnected> {
    pub fn open(addr: &str) -> io::Result<Self>;
}

impl Drop for Connection<Closed> {
    fn drop(&mut self) {
        close(self.fd);
    }
}
```

### 6.2 Builder + 内部可变性

```rust
pub struct SharedConfigBuilder {
    config: RefCell<PartialConfig>,
}

impl SharedConfigBuilder {
    pub fn set_host(&self, host: &str) {
        self.config.borrow_mut().host = Some(host.to_string());
    }
}
```

---

## 七、总结

### 7.1 映射总览

| 理论约束 | 设计模式 | 核心思想 |
|:---------|:---------|:---------|
| 线性逻辑 | RAII | 资源恰好使用一次 |
| 仿射类型 | Builder | 0次或1次使用 |
| 区域类型 | 类型状态 | 编译期状态检查 |
| 借用规则 | 访问者 | 分离遍历和修改 |
| 内部可变性 | Newtype | 隐藏的可变性 |
| 生命周期 | 零拷贝 | 引用有效期 |
| 'static | 单例 | 全局状态 |
| Send | 线程池 | 所有权转移 |
| Sync | 读写锁 | 共享引用 |

### 7.2 设计建议

1. **从约束出发**: 理解理论约束，让约束指导设计
2. **选择合适模式**: 根据约束选择最自然的模式
3. **组合模式**: 复杂场景可以组合多个模式
4. **验证安全性**: 确保模式使用符合理论约束

---

*本文档建立了从形式化理论到设计模式的完整桥梁*
