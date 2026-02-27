# 所有权转移决策树

> **创建日期**: 2026-02-24
> **最后更新**: 2026-02-28
> **状态**: ✅ 已扩展
> **版本**: Rust 1.93.0+ (Edition 2024)

---

## 概述

所有权转移决策树帮助开发者在不同场景下选择正确的所有权策略，包括移动、复制、借用、共享等模式。

---

## 主决策树

```text
┌─────────────────────────────────────────────────────────────────────┐
│                    所有权转移决策起点                               │
└───────────────────────────────┬─────────────────────────────────────┘
                                │
            ┌───────────────────┼───────────────────┐
            ▼                   ▼                   ▼
    ┌───────────────┐   ┌───────────────┐   ┌───────────────┐
    │ 数据量大?     │   │ 需要修改?     │   │ 多所有者?     │
    └───────┬───────┘   └───────┬───────┘   └───────┬───────┘
            │                   │                   │
        ┌───┴───┐           ┌───┴───┐           ┌───┴───┐
        ▼       ▼           ▼       ▼           ▼       ▼
      [是]    [否]        [是]    [否]        [是]    [否]
        │       │           │       │           │       │
        ▼       │           ▼       │           ▼       │
    ┌───────────┴───┐   ┌───────────┴───┐   ┌───────────┴───┐
    │ Box<T>        │   │ &mut T        │   │ Rc<T>/Arc<T>  │
    │ 堆分配所有权  │   │ 可变借用      │   │ 共享所有权    │
    └───────────────┘   └───────────────┘   └───────────────┘
```

## 决策流程

```text
数据需要如何使用？
│
├── 单一所有者
│   ├── 需要转移所有权
│   │   ├── 值较大 → 使用Box<T>
│   │   └── 值较小 → 直接Move
│   │
│   └── 不需要转移
│       ├── 固定大小 → 栈分配
│       └── 动态大小 → 使用Vec/String
│
├── 多所有者
│   ├── 只读共享
│   │   ├── 编译期确定 → 使用引用&
│   │   └── 运行期共享 → 使用Rc<T>
│   │       └── 跨线程 → 使用Arc<T>
│   │
│   └── 可变共享
│       ├── 单线程 → 使用RefCell<T> + Rc<T>
│       └── 跨线程 → 使用Mutex<T> + Arc<T>
│               └── 或 RwLock<T> + Arc<T>
│
└── 特殊场景
    ├── 循环引用
    │   └── 使用Weak<T>
    │
    └── 临时借用
        └── 使用& / &mut
---

## 场景一：函数参数传递

### 决策流程

```

函数需要获取参数?
│
├─ 完全所有权 (消费)
│  └─ 使用 T
│     └─ 调用者失去所有权
│        └─ 例: fn process(data: Vec<u8>)
│
├─ 只读访问
│  └─ 使用 &T
│     └─ 调用者保留所有权
│        └─ 例: fn print(data: &String)
│
└─ 修改权限
   └─ 使用 &mut T
      └─ 调用者保留所有权，可修改
         └─ 例: fn clear(data: &mut Vec<u8>)

```

### 代码示例

```rust
// 场景1: 消费所有权
fn take_ownership(s: String) {
    println!("{}", s);
} // s在这里drop

let s = String::from("hello");
take_ownership(s);
// s不再可用

// 场景2: 借用
fn borrow(s: &String) {
    println!("{}", s);
}

let s = String::from("hello");
borrow(&s);
println!("{}", s); // s仍然可用

// 场景3: 可变借用
fn modify(v: &mut Vec<i32>) {
    v.push(42);
}

let mut v = vec![1, 2, 3];
modify(&mut v);
println!("{:?}", v); // [1, 2, 3, 42]
```

---

## 场景二：返回值策略

### 决策流程

```
函数需要返回数据?
│
├─ 新创建的数据
│  └─ 直接返回 T
│     └─ 所有权转移给调用者
│        └─ 例: fn create() -> String
│
├─ 输入数据的引用
│  ├─ 生命周期足够长?
│  │  ├─ 是 → 返回 &'a T
│  │  └─ 否 → 返回 T (克隆)
│  └─ 例: fn first(s: &str) -> &str
│
└─ 可能不存在的值
   └─ 返回 Option<T> 或 Result<T, E>
      └─ 例: fn find() -> Option<&T>
```

### 代码示例

```rust
// 返回新创建的数据
fn create_greeting(name: &str) -> String {
    format!("Hello, {}!", name)
}

// 返回引用
fn find_first_word(s: &str) -> &str {
    s.split_whitespace().next().unwrap_or(s)
}

// 返回Option
fn find_user(id: u64) -> Option<User> {
    database.get(&id).cloned()
}
```

---

## 场景三：集合元素所有权

## 选择矩阵

| 场景 | 类型 | 线程安全 |
| :--- | :--- | :--- |
| 单所有 | `Box<T>` | 取决于T |
| 多共享只读 | `Rc<T>` | ❌ |
| 多共享只读(跨线程) | `Arc<T>` | ✅ |
| 多可变(单线程) | `Rc<RefCell<T>>` | ❌ |
| 多可变(跨线程) | `Arc<Mutex<T>>` | ✅ |
| 循环引用 | `Weak<T>` | 取决于容器 |

---

### 决策流程

```
存储在集合中?
│
├─ Vec<T> - 可变序列
│  ├─ push: 转移所有权
│  ├─ pop: 转移所有权出来
│  └─ get: 借用
│
├─ HashMap<K, V> - 键值对
│  ├─ insert: 转移K和V所有权
│  ├─ get: 借用V
│  └─ remove: 转移所有权出来
│
└─ HashSet<T> - 唯一集合
   ├─ insert: 转移所有权
   └─ contains: 借用
```

### 代码示例

```rust
// Vec所有权
let mut vec = Vec::new();
let s = String::from("hello");
vec.push(s); // s所有权转移给vec
// s不可用

let retrieved = vec.pop().unwrap(); // 所有权转移出来
println!("{}", retrieved);

// HashMap所有权
let mut map = HashMap::new();
map.insert("key", String::from("value"));

if let Some(v) = map.get("key") {
    println!("{}", v); // 借用
}

let removed = map.remove("key").unwrap(); // 所有权转移
```

---

## 场景四：多所有者场景

### 决策流程

```
需要多所有者?
│
├─ 单线程
│  └─ Rc<T> (引用计数)
│     ├─ clone(): 增加计数，共享
│     └─ drop: 减少计数
│
├─ 多线程
│  └─ Arc<T> (原子引用计数)
│     ├─ clone(): 增加计数，跨线程共享
│     └─ 需要内部可变性时配合Mutex/RwLock
│
└─ 需要修改
   └─ Rc<RefCell<T>> 或 Arc<Mutex<T>>
      └─ 运行时借用检查
```

### 代码示例

```rust
// 单所有
let data = Box::new(vec![1, 2, 3]);

// 多共享
let shared = Rc::new(vec![1, 2, 3]);
let shared2 = Rc::clone(&shared);

// 跨线程共享
let thread_safe = Arc::new(Mutex::new(0));
let thread_safe2 = Arc::clone(&thread_safe);
```

```rust
use std::rc::Rc;
use std::sync::Arc;
use std::cell::RefCell;
use std::sync::Mutex;

// 单线程多所有权
let data = Rc::new(String::from("shared"));
let data2 = Rc::clone(&data);
let data3 = Rc::clone(&data);
println!("count: {}", Rc::strong_count(&data)); // 3

// 多线程多所有权
let data = Arc::new(String::from("thread-safe"));
let data2 = Arc::clone(&data);
std::thread::spawn(move || {
    println!("{}", data2);
});

// 多线程+内部可变性
let counter = Arc::new(Mutex::new(0));
let counter2 = Arc::clone(&counter);
std::thread::spawn(move || {
    *counter2.lock().unwrap() += 1;
});
```

---

## 场景五：生命周期管理

### 决策流程

```
引用生命周期选择?
│
├─ 函数参数引用
│  └─ 输入生命周期参数
│     └─ fn foo<'a>(x: &'a T)
│
├─ 返回引用
│  └─ 必须与输入关联
│     └─ fn foo<'a>(x: &'a T) -> &'a U
│
├─ 结构体持有引用
│  └─ 结构体声明生命周期
│     └─ struct S<'a> { r: &'a T }
│
└─ 'static
   └─ 整个程序生命周期
      └─ 字符串字面量、全局常量
```

---

## 场景六：智能指针选择

| 需求 | 智能指针 | 所有权 | 可变性 | 开销 |
| :--- | :--- | :--- | :--- | :--- |
| 堆分配 | `Box<T>` | 唯一 | 可变 | 低 |
| 共享(单线程) | `Rc<T>` | 共享 | 不可变 | 引用计数 |
| 共享(多线程) | `Arc<T>` | 共享 | 不可变 | 原子计数 |
| 内部可变(单) | `RefCell<T>` | 唯一 | 运行时检查 | 借用检查 |
| 内部可变(多) | `Mutex<T>` | 共享 | 锁保护 | 锁开销 |
| 惰性初始化 | `LazyCell<T>` | 唯一 | 一次写入 | 无(首次后) |

---

## 常见反模式

| 反模式 | 问题 | 正确做法 |
| :--- | :--- | :--- |
| `fn take(s: &String)` → clone | 不必要的克隆 | `fn take(s: String)` |
| `fn return() -> &T` | 悬垂引用 | 返回 `T` 或 `Box<T>` |
| `Rc<RefCell<T>>`跨线程 | 编译错误 | 使用 `Arc<Mutex<T>>` |
| `&mut self` 方法返回 `&T` | 借用冲突 | 返回所有权或克隆 |
| 忘记`Arc::clone` | 所有权转移 | 显式克隆增加计数 |

---

## 与核心定理关联

| 决策 | 相关定理 | 说明 |
| :--- | :--- | :--- |
| 移动语义 | T-OW2 | 所有权唯一性保证 |
| 借用检查 | T-BR1 | 数据竞争自由保证 |
| 生命周期 | LF-T1 | 引用有效性保证 |
| Send/Sync | T-ASYNC | 线程安全保证 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 已扩展 - 所有权转移决策树完整版
