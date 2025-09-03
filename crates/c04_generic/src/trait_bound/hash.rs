/*
Hash trait 是 Rust 中用于哈希计算的重要特征。
它定义了 `hash` 方法，允许类型计算其哈希值。

## 定义

Hash trait 定义了一个 `hash` 方法：

```rust
pub trait Hash {
    fn hash<H: Hasher>(&self, state: &mut H);
}
```

## 重要特性

1. **哈希计算**: 为类型提供哈希值计算能力
2. **一致性**: 相等的值必须产生相同的哈希值
3. **自动派生**: 可以通过 `#[derive(Hash)]` 自动实现
4. **集合支持**: 为 HashMap、HashSet 等集合提供支持

## 哈希一致性要求

### 1. 相等性一致性
如果 a == b，那么 hash(a) == hash(b)

### 2. 稳定性
同一对象的哈希值在程序运行期间应该保持一致

### 3. 分布性
哈希值应该均匀分布，减少冲突

## 实现示例

### 1. 基本结构体实现 Hash

```rust
#[derive(Hash, Eq, PartialEq)]
struct Point {
    x: i32,
    y: i32,
}

// 手动实现
impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl Eq for Point { }

impl Hash for Point {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.x.hash(state);
        self.y.hash(state);
    }
}
```

### 2. 泛型类型实现 Hash

```rust
#[derive(Hash, Eq, PartialEq)]
struct Container<T: Hash + Eq> {
    value: T,
    count: usize,
}

impl<T: Hash + Eq> PartialEq for Container<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.count == other.count
    }
}

impl<T: Hash + Eq> Eq for Container<T> { }

impl<T: Hash + Eq> Hash for Container<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
        self.count.hash(state);
    }
}
```

### 3. 枚举实现 Hash

```rust
#[derive(Hash, Eq, PartialEq)]
enum Status {
    Idle,
    Active,
    Error(String),
}

impl PartialEq for Status {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Status::Idle, Status::Idle) => true,
            (Status::Active, Status::Active) => true,
            (Status::Error(s1), Status::Error(s2)) => s1 == s2,
            _ => false,
        }
    }
}

impl Eq for Status { }

impl Hash for Status {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Status::Idle => {
                0u8.hash(state); // 变体标识符
            }
            Status::Active => {
                1u8.hash(state); // 变体标识符
            }
            Status::Error(s) => {
                2u8.hash(state); // 变体标识符
                s.hash(state);   // 关联数据
            }
        }
    }
}
```

## 使用场景

### 1. 集合操作

```rust
use std::collections::HashMap;

fn main() {
    let mut map: HashMap<Point, String> = HashMap::new();
    
    let p1 = Point { x: 1, y: 2 };
    let p2 = Point { x: 1, y: 2 };
    
    map.insert(p1, "First point".to_string());
    
    // 由于 p1 == p2，所以 p2 也能找到相同的值
    if let Some(value) = map.get(&p2) {
        println!("Found: {}", value);
    }
}
```

### 2. 去重

```rust
use std::collections::HashSet;

fn main() {
    let mut set: HashSet<Point> = HashSet::new();
    
    let points = vec![
        Point { x: 1, y: 2 },
        Point { x: 3, y: 4 },
        Point { x: 1, y: 2 }, // 重复
        Point { x: 5, y: 6 },
    ];
    
    for point in points {
        set.insert(point);
    }
    
    println!("Unique points: {}", set.len()); // 3
}
```

### 3. 缓存键

```rust
use std::collections::HashMap;

struct Cache {
    data: HashMap<String, i32>,
}

impl Cache {
    fn new() -> Self {
        Cache {
            data: HashMap::new(),
        }
    }
    
    fn get_or_compute(&mut self, key: &str, compute: fn() -> i32) -> i32 {
        if let Some(&value) = self.data.get(key) {
            value
        } else {
            let value = compute();
            self.data.insert(key.to_string(), value);
            value
        }
    }
}
```

## 性能考虑

1. **哈希质量**: 实现高质量的哈希算法
2. **计算效率**: 避免在哈希计算中进行昂贵的操作
3. **冲突减少**: 减少哈希冲突的可能性
4. **内存使用**: 控制哈希计算的内存开销

## 最佳实践

1. **一致性**: 确保 Hash 实现与 Eq 一致
2. **性能**: 实现高效的哈希算法
3. **分布性**: 使用良好的哈希分布
4. **测试**: 为哈希一致性编写测试

## 高级用法

### 1. 自定义哈希算法

```rust
impl Hash for CustomType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // 自定义哈希逻辑
        self.important_field.hash(state);
        // 忽略某些字段
        // self.ignored_field.hash(state);
    }
}
```

### 2. 组合哈希

```rust
impl Hash for ComplexType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // 组合多个字段的哈希
        self.field1.hash(state);
        self.field2.hash(state);
        self.field3.hash(state);
        
        // 添加一些"盐"来改善分布
        0x12345678u32.hash(state);
    }
}
```

### 3. 条件哈希

```rust
impl Hash for ConditionalType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // 根据条件选择不同的哈希策略
        if self.use_simple_hash {
            self.id.hash(state);
        } else {
            self.id.hash(state);
            self.name.hash(state);
            self.metadata.hash(state);
        }
    }
}
```

## 总结

Hash trait 为 Rust 提供了哈希计算支持。
通过正确实现 Hash，可以创建高效的集合操作，
同时需要注意哈希一致性和性能影响。
*/

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

// 示例结构体
#[derive(Debug)]
pub struct HashExample {
    pub name: String,
    pub value: i32,
    pub active: bool,
}

impl PartialEq for HashExample {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && 
        self.value == other.value && 
        self.active == other.active
    }
}

impl Eq for HashExample { }

impl Hash for HashExample {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.value.hash(state);
        self.active.hash(state);
    }
}

// 泛型容器
#[derive(Debug)]
pub struct HashContainer<T: Hash + Eq> {
    pub value: T,
    pub metadata: String,
}

impl<T: Hash + Eq> PartialEq for HashContainer<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.metadata == other.metadata
    }
}

impl<T: Hash + Eq> Eq for HashContainer<T> { }

impl<T: Hash + Eq> Hash for HashContainer<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
        self.metadata.hash(state);
    }
}

// 状态枚举
#[derive(Debug)]
pub enum HashStatus {
    Idle,
    Active,
    Error(String),
}

impl PartialEq for HashStatus {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (HashStatus::Idle, HashStatus::Idle) => true,
            (HashStatus::Active, HashStatus::Active) => true,
            (HashStatus::Error(s1), HashStatus::Error(s2)) => s1 == s2,
            _ => false,
        }
    }
}

impl Eq for HashStatus { }

impl Hash for HashStatus {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            HashStatus::Idle => {
                0u8.hash(state); // 变体标识符
            }
            HashStatus::Active => {
                1u8.hash(state); // 变体标识符
            }
            HashStatus::Error(s) => {
                2u8.hash(state); // 变体标识符
                s.hash(state);   // 关联数据
            }
        }
    }
}

// 几何点
#[derive(Debug)]
pub struct HashPoint {
    pub x: i32,
    pub y: i32,
}

impl PartialEq for HashPoint {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl Eq for HashPoint { }

impl Hash for HashPoint {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.x.hash(state);
        self.y.hash(state);
    }
}

// 演示函数
pub fn demonstrate_hash() {
    // 基本哈希计算
    let p1 = HashPoint { x: 1, y: 2 };
    let p2 = HashPoint { x: 1, y: 2 };
    
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();
    
    p1.hash(&mut hasher1);
    p2.hash(&mut hasher2);
    
    let hash1 = hasher1.finish();
    let hash2 = hasher2.finish();
    
    println!("p1 hash: {}", hash1);
    println!("p2 hash: {}", hash2);
    println!("Hashes equal: {}", hash1 == hash2); // true
    
    // 结构体哈希
    let e1 = HashExample {
        name: String::from("Test"),
        value: 42,
        active: true,
    };
    
    let mut hasher = DefaultHasher::new();
    e1.hash(&mut hasher);
    let hash = hasher.finish();
    
    println!("Example hash: {}", hash);
    
    // 枚举哈希
    let s1 = HashStatus::Active;
    let s2 = HashStatus::Error(String::from("Something went wrong"));
    
    let mut hasher = DefaultHasher::new();
    s1.hash(&mut hasher);
    let hash1 = hasher.finish();
    
    let mut hasher = DefaultHasher::new();
    s2.hash(&mut hasher);
    let hash2 = hasher.finish();
    
    println!("Status1 hash: {}", hash1);
    println!("Status2 hash: {}", hash2);
    
    // 集合操作演示
    demonstrate_collection_operations();
    
    // 哈希一致性测试
    test_hash_consistency();
}

// 集合操作演示
fn demonstrate_collection_operations() {
    use std::collections::HashMap;
    use std::collections::HashSet;
    
    // HashMap 使用
    let mut map: HashMap<HashPoint, String> = HashMap::new();
    
    let p1 = HashPoint { x: 1, y: 2 };
    let p2 = HashPoint { x: 3, y: 4 };
    let p3 = HashPoint { x: 1, y: 2 }; // 与 p1 相等
    
    map.insert(p1, "First point".to_string());
    map.insert(p2, "Second point".to_string());
    
    // 由于 p1 == p3，所以 p3 也能找到相同的值
    if let Some(value) = map.get(&p3) {
        println!("Found point: {}", value);
    }
    
    // HashSet 使用
    let mut set: HashSet<HashPoint> = HashSet::new();
    
    let points = vec![
        HashPoint { x: 1, y: 2 },
        HashPoint { x: 3, y: 4 },
        HashPoint { x: 1, y: 2 }, // 重复
        HashPoint { x: 5, y: 6 },
    ];
    
    for point in points {
        set.insert(point);
    }
    
    println!("Unique points count: {}", set.len()); // 3
    println!("Set contents:");
    for point in &set {
        println!("  {:?}", point);
    }
}

// 哈希一致性测试
fn test_hash_consistency() {
    let p1 = HashPoint { x: 1, y: 2 };
    let p2 = HashPoint { x: 1, y: 2 };
    
    // 测试相等性一致性
    assert_eq!(p1, p2, "Points should be equal");
    
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();
    
    p1.hash(&mut hasher1);
    p2.hash(&mut hasher2);
    
    let hash1 = hasher1.finish();
    let hash2 = hasher2.finish();
    
    assert_eq!(hash1, hash2, "Equal objects should have equal hashes");
    
    println!("Hash consistency test passed!");
}

// 泛型哈希函数
pub fn calculate_hash<T: Hash>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_hash_example() {
        let e1 = HashExample {
            name: String::from("Test"),
            value: 100,
            active: false,
        };
        
        let e2 = HashExample {
            name: String::from("Test"),
            value: 100,
            active: false,
        };
        
        assert_eq!(e1, e2);
        
        let hash1 = calculate_hash(&e1);
        let hash2 = calculate_hash(&e2);
        
        assert_eq!(hash1, hash2);
    }
    
    #[test]
    fn test_point_hash() {
        let p1 = HashPoint { x: 1, y: 2 };
        let p2 = HashPoint { x: 1, y: 2 };
        let p3 = HashPoint { x: 2, y: 1 };
        
        assert_eq!(p1, p2);
        assert_ne!(p1, p3);
        
        let hash1 = calculate_hash(&p1);
        let hash2 = calculate_hash(&p2);
        let hash3 = calculate_hash(&p3);
        
        assert_eq!(hash1, hash2);
        assert_ne!(hash1, hash3);
    }
    
    #[test]
    fn test_status_hash() {
        let s1 = HashStatus::Active;
        let s2 = HashStatus::Active;
        let s3 = HashStatus::Idle;
        
        assert_eq!(s1, s2);
        assert_ne!(s1, s3);
        
        let hash1 = calculate_hash(&s1);
        let hash2 = calculate_hash(&s2);
        let hash3 = calculate_hash(&s3);
        
        assert_eq!(hash1, hash2);
        assert_ne!(hash1, hash3);
    }
    
    #[test]
    fn test_hash_consistency() {
        let p1 = HashPoint { x: 1, y: 2 };
        let p2 = HashPoint { x: 1, y: 2 };
        
        assert_eq!(p1, p2);
        
        let hash1 = calculate_hash(&p1);
        let hash2 = calculate_hash(&p2);
        
        assert_eq!(hash1, hash2);
    }
}
