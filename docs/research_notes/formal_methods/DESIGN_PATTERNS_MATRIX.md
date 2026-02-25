# 设计模式矩阵

> **创建日期**: 2026-02-24
> **状态**: ✅ 新建
> **用途**: 23种设计模式在Rust中的表达

---

## 创建型模式 (Creational)

| 模式 | Rust表达 | 难度 | 惯用法 | 说明 |
| :--- | :--- | :--- | :--- | :--- |
| **Singleton** | ⚠️ 受限 | 中 | `lazy_static` / `OnceLock` | Rust不鼓励全局状态 |
| **Factory Method** | ✅ 直接 | 低 | 泛型 + Trait | Rust天然支持 |
| **Abstract Factory** | ✅ 直接 | 低 | Trait组合 | 类型系统直接支持 |
| **Builder** | ✅ 直接 | 低 | 消耗式Builder | 所有权语义契合 |
| **Prototype** | ⚠️ 受限 | 中 | `Clone` trait | 需要显式实现Clone |

### Singleton在Rust

```rust
// 现代Rust使用std::sync::OnceLock
use std::sync::OnceLock;

static INSTANCE: OnceLock<Config> = OnceLock::new();

fn get_config() -> &'static Config {
    INSTANCE.get_or_init(|| Config::new())
}
```

**为什么不鼓励**: Rust倾向于显式依赖注入，而非全局状态。

---

## 结构型模式 (Structural)

| 模式 | Rust表达 | 难度 | 惯用法 | 说明 |
| :--- | :--- | :--- | :--- | :--- |
| **Adapter** | ✅ 直接 | 低 | Trait实现 + 包装 | 类型系统支持 |
| **Bridge** | ✅ 直接 | 低 | Trait组合 | 分离抽象与实现 |
| **Composite** | ⚠️ 受限 | 中 | `Rc<RefCell>` | 所有权限制递归结构 |
| **Decorator** | ✅ 直接 | 低 | Trait组合 | 零成本抽象 |
| **Facade** | ✅ 直接 | 低 | 模块系统 | 模块即Facade |
| **Flyweight** | ✅ 直接 | 低 | 生命周期管理 | 共享不可变数据 |
| **Proxy** | ✅ 直接 | 低 | `Deref` / 智能指针 | 标准库已有 |

### Composite的Rust实现

```rust
// 使用Rc<RefCell>实现父子关系
type NodeRef = Rc<RefCell<Node>>;

struct Node {
    value: i32,
    children: Vec<NodeRef>,
}

impl Node {
    fn sum(&self) -> i32 {
        self.value + self.children.iter()
            .map(|c| c.borrow().sum())
            .sum::<i32>()
    }
}
```

**限制**: `Rc<RefCell>`有运行时开销，不如C++直接指针高效。

---

## 行为型模式 (Behavioral)

| 模式 | Rust表达 | 难度 | 惯用法 | 说明 |
| :--- | :--- | :--- | :--- | :--- |
| **Chain of Responsibility** | ✅ 直接 | 低 | 链表/迭代器 | 所有权清晰 |
| **Command** | ✅ 直接 | 低 | 闭包 / Trait对象 | 闭包即命令 |
| **Interpreter** | ✅ 直接 | 中 | 枚举 + 递归 | 模式匹配优势 |
| **Iterator** | ✅ 直接 | 低 | `Iterator` trait | 语言内置支持 |
| **Mediator** | ✅ 直接 | 中 | channel / 事件总线 | mpsc天生适合 |
| **Memento** | ⚠️ 受限 | 中 | 序列化 / 深拷贝 | 需要Clone |
| **Observer** | ✅ 直接 | 中 | channel / 回调 | channel更Rusty |
| **State** | ✅ 直接 | 低 | 枚举 + 方法 | 代数数据类型优势 |
| **Strategy** | ✅ 直接 | 低 | Trait对象 / 泛型 | 零成本抽象 |
| **Template Method** | ✅ 直接 | 低 | Trait默认方法 | 类型系统支持 |
| **Visitor** | ⚠️ 受限 | 高 | 枚举匹配 | 缺少双重分发 |

### State模式Rust风格

```rust
// 使用枚举+方法，而非继承
enum State {
    Draft,
    Review { reviewer: String },
    Published,
}

impl Document {
    fn approve(&mut self) -> Result<(), Error> {
        match self.state {
            State::Review { .. } => {
                self.state = State::Published;
                Ok(())
            }
            _ => Err(Error::InvalidState),
        }
    }
}
```

**优势**: 枚举保证状态转换完整性，编译器检查遗漏。

---

## 模式对比总结

### 表达力评估

| 类别 | 直接表达 | 受限表达 | 总计 |
| :--- | :--- | :--- | :--- |
| 创建型 | 3 | 2 | 5 |
| 结构型 | 6 | 1 | 7 |
| 行为型 | 9 | 2 | 11 |
| **总计** | **18** | **5** | **23** |

**78%的设计模式在Rust中可以直接表达**。

### 受限模式分析

| 模式 | 限制原因 | Rust解决方案 |
| :--- | :--- | :--- |
| Singleton | 不鼓励全局状态 | OnceLock / 依赖注入 |
| Composite | 所有权限制循环引用 | `Rc<RefCell>` / Arena分配器 |
| Prototype | 缺少反射 / 默认深拷贝 | 显式Clone实现 |
| Memento | 需要深拷贝 | 序列化 / 手动Clone |
| Visitor | 缺少双重分发 | 枚举匹配 / 泛型方法 |

---

## Rust独特优势

### 1. 枚举+模式匹配替代Visitor

```rust
// Rust风格：枚举+match
enum Expr {
    Num(i32),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
}

fn eval(e: &Expr) -> i32 {
    match e {
        Expr::Num(n) => *n,
        Expr::Add(a, b) => eval(a) + eval(b),
        Expr::Mul(a, b) => eval(a) * eval(b),
    }
}
```

比Visitor模式更简洁，编译器检查穷尽性。

### 2. Trait组合替代继承

```rust
// 组合多个trait
trait Readable { fn read(&mut self, buf: &mut [u8]) -> Result<usize>; }
trait Writable { fn write(&mut self, buf: &[u8]) -> Result<usize>; }
trait Seekable { fn seek(&mut self, pos: SeekFrom) -> Result<u64>; }

// 灵活组合，无需继承层次
struct File;  // 实现全部三个
truct Socket; // 只实现Read+Write
```

### 3. 零成本抽象

```rust
// Strategy模式：泛型实现零成本
fn process<T: Strategy>(data: Data, strategy: T) -> Result {
    strategy.execute(data)  // 单态化，无虚函数开销
}
```

---

## 选择决策

```text
需要设计模式？
├── 创建对象？
│   ├── 单一类型 → Factory Method
│   ├── 多种相关产品 → Abstract Factory
│   ├── 复杂构造 → Builder
│   └── 全局唯一 → 谨慎使用Singleton
│
├── 组合对象？
│   ├── 统一接口 → Adapter
│   ├── 树形结构 → Composite (用Rc<RefCell>)
│   ├── 动态添加功能 → Decorator
│   └── 简化接口 → Facade
│
└── 行为变化？
    ├── 算法族 → Strategy
    ├── 状态机 → State (用枚举)
    ├── 请求队列 → Command
    ├── 一对多通知 → Observer (用channel)
    └── 遍历集合 → Iterator (语言内置)
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 设计模式矩阵
