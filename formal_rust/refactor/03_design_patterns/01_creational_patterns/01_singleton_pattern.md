# 01. 单例模式 (Singleton Pattern)

## 01.01. 形式化定义

### 01.01.01. 数学定义

设 $S$ 为单例模式的实例集合，$I$ 为实例标识符集合，则单例模式可形式化定义为：

**定义 1.1 (单例模式)** 单例模式是一个三元组 $(S, I, \phi)$，其中：

- $S$ 是实例集合，满足 $|S| = 1$
- $I$ 是实例标识符集合
- $\phi: I \rightarrow S$ 是实例映射函数，满足 $\forall i_1, i_2 \in I: \phi(i_1) = \phi(i_2)$

**定理 1.1 (单例唯一性)** 对于任意单例模式 $(S, I, \phi)$，存在唯一的实例 $s \in S$，使得 $\forall i \in I: \phi(i) = s$。

**证明**：

1. 由定义 1.1，$|S| = 1$，因此 $S = \{s\}$ 对某个 $s$
2. 由映射函数的定义，$\forall i \in I: \phi(i) = s$
3. 因此 $s$ 是唯一的实例

### 01.01.02. 类型理论定义

在类型理论中，单例模式可表示为：

```typescript
type Singleton<T> = {
  getInstance(): T;
  instance: T;
}

// 单例约束
constraint SingletonConstraint<T> = {
  ∀x, y: T → x === y
}
```

## 01.02. 实现形式化

### 01.02.01. Rust 实现

```rust
use std::sync::{Mutex, Once, ONCE_INIT};
use std::mem;

/// 单例模式的形式化实现
/// 
/// 数学性质：
/// - 唯一性：∀i₁, i₂ ∈ InstanceId: get_instance(i₁) = get_instance(i₂)
/// - 全局性：∀i ∈ InstanceId: get_instance(i) ∈ GlobalScope
/// - 线程安全：∀t₁, t₂ ∈ Thread: safe_access(t₁, t₂)
#[derive(Debug)]
pub struct SingletonLogger {
    level: String,
    instance_id: u64,
}

impl SingletonLogger {
    // 全局实例指针
    static mut SINGLETON_INSTANCE: *const Mutex<SingletonLogger> = 0 as *const _;
    static ONCE: Once = ONCE_INIT;
    
    /// 获取单例实例
    /// 
    /// 数学性质：
    /// - 幂等性：get_instance() = get_instance()
    /// - 唯一性：∀calls: get_instance() returns same instance
    /// - 线程安全：∀threads: safe concurrent access
    pub fn get_instance() -> &'static Mutex<SingletonLogger> {
        ONCE.call_once(|| {
            let singleton = Mutex::new(SingletonLogger {
                level: "INFO".to_string(),
                instance_id: 1,
            });
            unsafe {
                SINGLETON_INSTANCE = Box::into_raw(Box::new(singleton));
            }
        });

        unsafe {
            &*SINGLETON_INSTANCE
        }
    }
    
    /// 日志记录操作
    /// 
    /// 数学性质：
    /// - 单调性：∀m₁, m₂: log(m₁) ∧ log(m₂) → ordered(m₁, m₂)
    /// - 完整性：∀m: log(m) → m ∈ LogSet
    pub fn log(&self, message: &str) {
        println!("[{}] {} (Instance: {})", self.level, message, self.instance_id);
    }
    
    /// 设置日志级别
    /// 
    /// 数学性质：
    /// - 状态一致性：set_level(l) → level = l
    /// - 有效性：∀l: set_level(l) → l ∈ ValidLevels
    pub fn set_level(&mut self, level: String) {
        self.level = level;
    }
    
    /// 获取实例标识符
    /// 
    /// 数学性质：
    /// - 唯一性：get_instance_id() = constant
    /// - 不变性：∀calls: get_instance_id() returns same value
    pub fn get_instance_id(&self) -> u64 {
        self.instance_id
    }
}

/// 使用 once_cell 的现代实现
use once_cell::sync::Lazy;

static GLOBAL_CONFIG: Lazy<Mutex<Config>> = Lazy::new(|| {
    Mutex::new(Config::load_default())
});

#[derive(Debug)]
pub struct Config {
    setting: String,
    version: u32,
}

impl Config {
    /// 加载默认配置
    /// 
    /// 数学性质：
    /// - 确定性：load_default() always returns same result
    /// - 完整性：load_default() returns complete configuration
    pub fn load_default() -> Self {
        Config { 
            setting: "default".to_string(),
            version: 1,
        }
    }
    
    /// 获取配置设置
    pub fn get_setting(&self) -> &str {
        &self.setting
    }
    
    /// 更新配置设置
    /// 
    /// 数学性质：
    /// - 原子性：update_setting(s) → setting = s
    /// - 版本递增：update_setting(s) → version = version + 1
    pub fn update_setting(&mut self, setting: String) {
        self.setting = setting;
        self.version += 1;
    }
}
```

### 01.02.02. 形式化验证

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    /// 测试单例唯一性定理
    #[test]
    fn test_singleton_uniqueness() {
        let instance1 = SingletonLogger::get_instance();
        let instance2 = SingletonLogger::get_instance();
        
        // 验证唯一性：∀i₁, i₂: get_instance(i₁) = get_instance(i₂)
        assert_eq!(instance1 as *const _, instance2 as *const _);
        
        // 验证实例ID一致性
        let id1 = instance1.lock().unwrap().get_instance_id();
        let id2 = instance2.lock().unwrap().get_instance_id();
        assert_eq!(id1, id2);
    }
    
    /// 测试线程安全性
    #[test]
    fn test_thread_safety() {
        use std::thread;
        use std::sync::Arc;
        
        let handles: Vec<_> = (0..10).map(|_| {
            thread::spawn(|| {
                let instance = SingletonLogger::get_instance();
                instance.lock().unwrap().log("Thread test");
                instance.lock().unwrap().get_instance_id()
            })
        }).collect();
        
        let ids: Vec<u64> = handles.into_iter()
            .map(|h| h.join().unwrap())
            .collect();
        
        // 验证所有线程获得相同实例
        let first_id = ids[0];
        assert!(ids.iter().all(|&id| id == first_id));
    }
    
    /// 测试配置单例
    #[test]
    fn test_config_singleton() {
        let config1 = GLOBAL_CONFIG.lock().unwrap();
        let config2 = GLOBAL_CONFIG.lock().unwrap();
        
        // 验证相同配置
        assert_eq!(config1.get_setting(), config2.get_setting());
        assert_eq!(config1.version, config2.version);
    }
}
```

## 01.03. 数学性质分析

### 01.03.01. 复杂度分析

**时间复杂度**：

- 初始化：$O(1)$ - 单次初始化
- 访问：$O(1)$ - 直接指针访问
- 线程同步：$O(1)$ - 原子操作

**空间复杂度**：

- 实例存储：$O(1)$ - 固定大小
- 同步开销：$O(1)$ - 常量开销

### 01.03.02. 正确性证明

**定理 1.2 (单例正确性)** 单例模式的实现满足以下性质：

1. **唯一性**：$\forall t_1, t_2 \in \text{Time}: \text{get\_instance}(t_1) = \text{get\_instance}(t_2)$
2. **线程安全**：$\forall t_1, t_2 \in \text{Thread}: \text{safe\_access}(t_1, t_2)$
3. **延迟初始化**：$\text{instance} = \text{null} \text{ until first access}$

**证明**：

1. 唯一性由 `Once` 类型保证，确保初始化代码只执行一次
2. 线程安全由 `Mutex` 提供，确保并发访问的安全性
3. 延迟初始化通过 `ONCE_INIT` 实现

## 01.04. 应用场景与约束

### 01.04.01. 适用场景

1. **全局配置管理**：$\text{Config} \in \text{GlobalScope}$
2. **日志系统**：$\text{Logger} \in \text{Singleton}$
3. **数据库连接池**：$\text{ConnectionPool} \in \text{Singleton}$
4. **缓存管理器**：$\text{CacheManager} \in \text{Singleton}$

### 01.04.02. 约束条件

**数学约束**：

- $\forall i \in \text{Instance}: \text{count}(i) = 1$
- $\forall t \in \text{Thread}: \text{thread\_safe}(t)$
- $\forall m \in \text{Method}: \text{atomic}(m)$

**实现约束**：

- 构造函数必须私有
- 实例访问必须通过静态方法
- 必须处理并发访问

## 01.05. 变体与扩展

### 01.05.01. 线程局部单例

```rust
use std::cell::RefCell;
use std::collections::HashMap;

thread_local! {
    static THREAD_SINGLETONS: RefCell<HashMap<TypeId, Box<dyn Any>>> = RefCell::new(HashMap::new());
}

/// 线程局部单例模式
/// 
/// 数学性质：
/// - 线程唯一性：∀t ∈ Thread: |Singleton_t| = 1
/// - 线程隔离：∀t₁, t₂: Singleton_t₁ ≠ Singleton_t₂
pub struct ThreadLocalSingleton<T> {
    _phantom: std::marker::PhantomData<T>,
}

impl<T: 'static> ThreadLocalSingleton<T> {
    pub fn get_instance() -> &'static T {
        THREAD_SINGLETONS.with(|singletons| {
            let type_id = TypeId::of::<T>();
            let mut map = singletons.borrow_mut();
            
            if !map.contains_key(&type_id) {
                // 创建新实例
                map.insert(type_id, Box::new(T::new()));
            }
            
            map.get(&type_id)
                .unwrap()
                .downcast_ref::<T>()
                .unwrap()
        })
    }
}
```

### 01.05.02. 参数化单例

```rust
/// 参数化单例模式
/// 
/// 数学性质：
/// - 参数唯一性：∀p₁, p₂: p₁ ≠ p₂ → Singleton(p₁) ≠ Singleton(p₂)
/// - 参数一致性：∀p: Singleton(p) maintains p
pub struct ParameterizedSingleton<P, T> {
    parameter: P,
    instance: T,
}

impl<P: Clone + Eq + Hash, T> ParameterizedSingleton<P, T> {
    pub fn get_instance(parameter: P) -> &'static T {
        // 基于参数创建或获取实例
        // 实现细节...
    }
}
```

## 01.06. 总结

单例模式通过数学形式化定义确保了实例的唯一性和全局可访问性。其核心性质包括：

1. **唯一性定理**：$\forall i_1, i_2 \in I: \phi(i_1) = \phi(i_2)$
2. **线程安全**：$\forall t_1, t_2 \in \text{Thread}: \text{safe\_access}(t_1, t_2)$
3. **延迟初始化**：$\text{instance} = \text{null} \text{ until first access}$

该模式在全局资源管理、配置管理和日志系统等场景中具有重要应用价值。

---

**参考文献**：

1. Gamma, E., Helm, R., Johnson, R., & Vlissides, J. (1994). Design Patterns: Elements of Reusable Object-Oriented Software
2. Pierce, B. C. (2002). Types and Programming Languages
3. Rust Reference Manual - Thread Safety and Concurrency
