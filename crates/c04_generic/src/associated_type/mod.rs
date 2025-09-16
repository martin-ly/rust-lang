/*
在 Rust 中，关联类型（associated types）是与特征（traits）相关联的类型参数。
它们允许在特征中定义一个类型，而不需要在实现特征时显式地指定该类型。
这使得代码更加简洁和易于理解。

## 定义
关联类型的定义通常在特征中进行，使用 `type` 关键字。
例如：

```rust
trait Iterator {
    type Item; // 关联类型的定义

    fn next(&mut self) -> Option<Self::Item>;
}
```

在这个例子中，`Iterator` 特征定义了一个关联类型 `Item`，它表示迭代器返回的元素类型。

## 重要特性

1. **类型关联**: 与特征紧密关联的类型
2. **简化泛型**: 减少泛型参数的数量
3. **类型安全**: 编译时类型检查
4. **实现清晰**: 使特征实现更加清晰

## 与泛型参数的区别

### 关联类型
```rust
trait Container {
    type Item;
    fn get(&self) -> Option<&Self::Item>;
}
```

### 泛型参数
```rust
trait Container<T> {
    fn get(&self) -> Option<&T>;
}
```

## 实现示例

### 1. 基本关联类型

```rust
trait Iterator {
    type Item;

    fn next(&mut self) -> Option<Self::Item>;
    fn count(&self) -> usize;
}

struct Counter {
    count: u32,
    max: u32,
}

impl Iterator for Counter {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        if self.count < self.max {
            self.count += 1;
            Some(self.count)
        } else {
            None
        }
    }

    fn count(&self) -> usize {
        self.count as usize
    }
}
```

### 2. 复杂关联类型

```rust
trait Graph {
    type Node;
    type Edge;

    fn nodes(&self) -> Vec<&Self::Node>;
    fn edges(&self) -> Vec<&Self::Edge>;
    fn add_node(&mut self, node: Self::Node);
    fn add_edge(&mut self, edge: Self::Edge);
}

struct SimpleGraph {
    nodes: Vec<String>,
    edges: Vec<(String, String)>,
}

impl Graph for SimpleGraph {
    type Node = String;
    type Edge = (String, String);

    fn nodes(&self) -> Vec<&Self::Node> {
        self.nodes.iter().collect()
    }

    fn edges(&self) -> Vec<&Self::Node> {
        self.edges.iter().flat_map(|(a, b)| vec![a, b]).collect()
    }

    fn add_node(&mut self, node: Self::Node) {
        self.nodes.push(node);
    }

    fn add_edge(&mut self, edge: Self::Edge) {
        self.edges.push(edge);
    }
}
```

### 3. 关联类型与泛型结合

```rust
trait Collection<T> {
    type Iterator: Iterator<Item = T>;
    type Key;

    fn iter(&self) -> Self::Iterator;
    fn get(&self, key: &Self::Key) -> Option<&T>;
    fn insert(&mut self, key: Self::Key, value: T);
}

struct HashMap<K, V> {
    data: std::collections::HashMap<K, V>,
}

impl<K, V> Collection<V> for HashMap<K, V>
where
    K: std::hash::Hash + Eq + Clone,
    V: Clone,
{
    type Iterator = std::collections::hash_map::Values<'static, K, V>;
    type Key = K;

    fn iter(&self) -> Self::Iterator {
        // 这里需要处理生命周期问题
        unimplemented!()
    }

    fn get(&self, key: &Self::Key) -> Option<&V> {
        self.data.get(key)
    }

    fn insert(&mut self, key: Self::Key, value: V) {
        self.data.insert(key, value);
    }
}
```

## 使用场景

### 1. 迭代器模式

```rust
trait Stream {
    type Item;
    type Error;

    fn next(&mut self) -> Result<Option<Self::Item>, Self::Error>;
    fn peek(&self) -> Result<Option<&Self::Item>, Self::Error>;
}

struct NumberStream {
    numbers: Vec<i32>,
    position: usize,
}

impl Stream for NumberStream {
    type Item = i32;
    type Error = String;

    fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
        if self.position < self.numbers.len() {
            let item = self.numbers[self.position];
            self.position += 1;
            Ok(Some(item))
        } else {
            Ok(None)
        }
    }

    fn peek(&self) -> Result<Option<&Self::Item>, Self::Error> {
        if self.position < self.numbers.len() {
            Ok(Some(&self.numbers[self.position]))
        } else {
            Ok(None)
        }
    }
}
```

### 2. 数据库抽象

```rust
trait Database {
    type Connection;
    type Transaction;
    type Error;

    fn connect(&self) -> Result<Self::Connection, Self::Error>;
    fn begin_transaction(&self, conn: &mut Self::Connection) -> Result<Self::Transaction, Self::Error>;
    fn commit(&self, transaction: Self::Transaction) -> Result<(), Self::Error>;
}

struct SqliteDatabase;

impl Database for SqliteDatabase {
    type Connection = String; // 简化为字符串
    type Transaction = String;
    type Error = String;

    fn connect(&self) -> Result<Self::Connection, Self::Error> {
        Ok("sqlite_connection".to_string())
    }

    fn begin_transaction(&self, _conn: &mut Self::Connection) -> Result<Self::Transaction, Self::Error> {
        Ok("sqlite_transaction".to_string())
    }

    fn commit(&self, _transaction: Self::Transaction) -> Result<(), Self::Error> {
        Ok(())
    }
}
```

### 3. 网络协议抽象

```rust
trait Protocol {
    type Message;
    type Response;
    type Error;

    fn encode(&self, message: &Self::Message) -> Result<Vec<u8>, Self::Error>;
    fn decode(&self, data: &[u8]) -> Result<Self::Message, Self::Error>;
    fn process(&self, message: Self::Message) -> Result<Self::Response, Self::Error>;
}

struct HttpProtocol;

impl Protocol for HttpProtocol {
    type Message = String;
    type Response = String;
    type Error = String;

    fn encode(&self, message: &Self::Message) -> Result<Vec<u8>, Self::Error> {
        Ok(message.as_bytes().to_vec())
    }

    fn decode(&self, data: &[u8]) -> Result<Self::Message, Self::Error> {
        String::from_utf8(data.to_vec()).map_err(|e| e.to_string())
    }

    fn process(&self, message: Self::Message) -> Result<Self::Response, Self::Error> {
        Ok(format!("HTTP Response: {}", message))
    }
}
```

## 高级用法

### 1. 关联类型约束

```rust
trait AdvancedIterator {
    type Item: Clone + std::fmt::Debug;
    type Key: std::hash::Hash + Eq;

    fn next(&mut self) -> Option<Self::Item>;
    fn key(&self) -> Option<&Self::Key>;
}

struct KeyValueIterator<K, V> {
    items: Vec<(K, V)>,
    position: usize,
}

impl<K, V> AdvancedIterator for KeyValueIterator<K, V>
where
    K: std::hash::Hash + Eq + Clone + std::fmt::Debug,
    V: Clone + std::fmt::Debug,
{
    type Item = V;
    type Key = K;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position < self.items.len() {
            let item = self.items[self.position].1.clone();
            self.position += 1;
            Some(item)
        } else {
            None
        }
    }

    fn key(&self) -> Option<&Self::Key> {
        if self.position < self.items.len() {
            Some(&self.items[self.position].0)
        } else {
            None
        }
    }
}
```

### 2. 关联类型与生命周期

```rust
trait Storage<'a> {
    type Item: 'a;
    type Iterator: Iterator<Item = &'a Self::Item>;

    fn iter(&'a self) -> Self::Iterator;
    fn get(&'a self, index: usize) -> Option<&'a Self::Item>;
}

struct VecStorage<T> {
    items: Vec<T>,
}

impl<'a, T> Storage<'a> for VecStorage<T>
where
    T: 'a,
{
    type Item = T;
    type Iterator = std::slice::Iter<'a, T>;

    fn iter(&'a self) -> Self::Iterator {
        self.items.iter()
    }

    fn get(&'a self, index: usize) -> Option<&'a Self::Item> {
        self.items.get(index)
    }
}
```

## 性能考虑

1. **零成本抽象**: 关联类型在编译时被解析
2. **类型安全**: 编译时类型检查，无运行时开销
3. **代码生成**: 为每个具体类型生成专用代码
4. **内存布局**: 不影响内存布局

## 最佳实践

1. **语义清晰**: 关联类型名称应该清晰表达其用途
2. **约束合理**: 为关联类型添加适当的约束
3. **文档完整**: 明确说明关联类型的含义和用途
4. **测试覆盖**: 为关联类型的不同实现编写测试

## 总结

关联类型为 Rust 提供了强大的类型抽象能力。
通过合理使用关联类型，可以创建更加清晰、类型安全的代码，
同时保持零成本抽象的优势。
*/

// 类型别名，改善代码可读性
type NodeList = Vec<String>;
type EdgeList = Vec<(String, String)>;
type NumberList = Vec<i32>;
type KeyValueList<K, V> = Vec<(K, V)>;
// type IteratorResult<T, E> = Result<Option<T>, E>;
// type PeekResult<'a, T, E> = Result<Option<&'a T>, E>;
// type ConnectionResult<T, E> = Result<T, E>;
// type TransactionResult<T, E> = Result<T, E>;

// 基本关联类型示例
pub trait Iterator {
    type Item;

    fn next(&mut self) -> Option<Self::Item>;
    fn count(&self) -> usize;
}

pub struct Counter {
    pub count: u32,
    pub max: u32,
}

impl Iterator for Counter {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        if self.count < self.max {
            self.count += 1;
            Some(self.count)
        } else {
            None
        }
    }

    fn count(&self) -> usize {
        self.count as usize
    }
}

// 图结构示例
pub trait Graph {
    type Node;
    type Edge;

    fn nodes(&self) -> Vec<&Self::Node>;
    fn edges(&self) -> Vec<&Self::Edge>;
    fn add_node(&mut self, node: Self::Node);
    fn add_edge(&mut self, edge: Self::Edge);
}

pub struct SimpleGraph {
    pub nodes: NodeList,
    pub edges: EdgeList,
}

impl Graph for SimpleGraph {
    type Node = String;
    type Edge = (String, String);

    fn nodes(&self) -> Vec<&Self::Node> {
        self.nodes.iter().collect()
    }

    fn edges(&self) -> Vec<&Self::Edge> {
        self.edges.iter().collect()
    }

    fn add_node(&mut self, node: Self::Node) {
        self.nodes.push(node);
    }

    fn add_edge(&mut self, edge: Self::Edge) {
        self.edges.push(edge);
    }
}

impl Default for SimpleGraph {
    fn default() -> Self {
        Self::new()
    }
}

impl SimpleGraph {
    pub fn new() -> Self {
        SimpleGraph {
            nodes: Vec::new(),
            edges: Vec::new(),
        }
    }
}

// 流处理示例
pub trait Stream {
    type Item;
    type Error;

    fn next(&mut self) -> Result<Option<Self::Item>, Self::Error>;
    fn peek(&self) -> Result<Option<&Self::Item>, Self::Error>;
}

pub struct NumberStream {
    pub numbers: NumberList,
    pub position: usize,
}

impl Stream for NumberStream {
    type Item = i32;
    type Error = String;

    fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
        if self.position < self.numbers.len() {
            let item = self.numbers[self.position];
            self.position += 1;
            Ok(Some(item))
        } else {
            Ok(None)
        }
    }

    fn peek(&self) -> Result<Option<&Self::Item>, Self::Error> {
        if self.position < self.numbers.len() {
            Ok(Some(&self.numbers[self.position]))
        } else {
            Ok(None)
        }
    }
}

impl NumberStream {
    pub fn new(numbers: Vec<i32>) -> Self {
        NumberStream {
            numbers,
            position: 0,
        }
    }
}

// 数据库抽象示例
pub trait Database {
    type Connection;
    type Transaction;
    type Error;

    fn connect(&self) -> Result<Self::Connection, Self::Error>;
    fn begin_transaction(
        &self,
        conn: &mut Self::Connection,
    ) -> Result<Self::Transaction, Self::Error>;
    fn commit(&self, transaction: Self::Transaction) -> Result<(), Self::Error>;
}

pub struct SqliteDatabase;

impl Database for SqliteDatabase {
    type Connection = String;
    type Transaction = String;
    type Error = String;

    fn connect(&self) -> Result<Self::Connection, Self::Error> {
        Ok("sqlite_connection".to_string())
    }

    fn begin_transaction(
        &self,
        _conn: &mut Self::Connection,
    ) -> Result<Self::Transaction, Self::Error> {
        Ok("sqlite_transaction".to_string())
    }

    fn commit(&self, _transaction: Self::Transaction) -> Result<(), Self::Error> {
        Ok(())
    }
}

// 高级迭代器示例
pub trait AdvancedIterator {
    type Item: Clone + std::fmt::Debug;
    type Key: std::hash::Hash + Eq;

    fn next(&mut self) -> Option<Self::Item>;
    fn key(&self) -> Option<&Self::Key>;
}

pub struct KeyValueIterator<K, V> {
    pub items: KeyValueList<K, V>,
    pub position: usize,
}

impl<K, V> AdvancedIterator for KeyValueIterator<K, V>
where
    K: std::hash::Hash + Eq + Clone + std::fmt::Debug,
    V: Clone + std::fmt::Debug,
{
    type Item = V;
    type Key = K;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position < self.items.len() {
            let item = self.items[self.position].1.clone();
            self.position += 1;
            Some(item)
        } else {
            None
        }
    }

    fn key(&self) -> Option<&Self::Key> {
        if self.position < self.items.len() {
            Some(&self.items[self.position].0)
        } else {
            None
        }
    }
}

impl<K, V> KeyValueIterator<K, V> {
    pub fn new(items: Vec<(K, V)>) -> Self {
        KeyValueIterator { items, position: 0 }
    }
}

// 演示函数
pub fn demonstrate_associated_types() {
    println!("=== Associated Types Demonstration ===\n");

    // 基本迭代器演示
    demonstrate_basic_iterator();

    // 图结构演示
    demonstrate_graph();

    // 流处理演示
    demonstrate_stream();

    // 数据库抽象演示
    demonstrate_database();

    // 高级迭代器演示
    demonstrate_advanced_iterator();
}

// 基本迭代器演示
fn demonstrate_basic_iterator() {
    println!("--- Basic Iterator Demo ---");

    let mut counter = Counter { count: 0, max: 5 };

    println!("Counter values:");
    while let Some(value) = counter.next() {
        println!("  {}", value);
    }

    println!("Total count: {}", counter.count());
    println!();
}

// 图结构演示
fn demonstrate_graph() {
    println!("--- Graph Demo ---");

    let mut graph = SimpleGraph::new();

    graph.add_node("A".to_string());
    graph.add_node("B".to_string());
    graph.add_node("C".to_string());

    graph.add_edge(("A".to_string(), "B".to_string()));
    graph.add_edge(("B".to_string(), "C".to_string()));

    println!("Nodes: {:?}", graph.nodes());
    println!("Edges: {:?}", graph.edges());
    println!();
}

// 流处理演示
fn demonstrate_stream() {
    println!("--- Stream Demo ---");

    let mut stream = NumberStream::new(vec![1, 2, 3, 4, 5]);

    println!("Stream values:");
    while let Ok(Some(value)) = stream.next() {
        println!("  {}", value);
    }
    println!();
}

// 数据库抽象演示
fn demonstrate_database() {
    println!("--- Database Demo ---");

    let db = SqliteDatabase;

    match db.connect() {
        Ok(conn) => {
            println!("Connected: {}", conn);

            let mut conn_mut = conn;
            match db.begin_transaction(&mut conn_mut) {
                Ok(transaction) => {
                    println!("Transaction started: {}", transaction);

                    match db.commit(transaction) {
                        Ok(()) => println!("Transaction committed successfully"),
                        Err(e) => println!("Commit error: {}", e),
                    }
                }
                Err(e) => println!("Transaction error: {}", e),
            }
        }
        Err(e) => println!("Connection error: {}", e),
    }
    println!();
}

// 高级迭代器演示
fn demonstrate_advanced_iterator() {
    println!("--- Advanced Iterator Demo ---");

    let items = vec![
        ("key1".to_string(), "value1".to_string()),
        ("key2".to_string(), "value2".to_string()),
        ("key3".to_string(), "value3".to_string()),
    ];

    let mut iterator = KeyValueIterator::new(items);

    println!("Key-value pairs:");
    while let Some(value) = iterator.next() {
        if let Some(key) = iterator.key() {
            println!("  {}: {}", key, value);
        }
    }
    println!();
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_counter() {
        let mut counter = Counter { count: 0, max: 3 };

        assert_eq!(counter.next(), Some(1));
        assert_eq!(counter.next(), Some(2));
        assert_eq!(counter.next(), Some(3));
        assert_eq!(counter.next(), None);
        assert_eq!(counter.count(), 3);
    }

    #[test]
    fn test_simple_graph() {
        let mut graph = SimpleGraph::new();

        graph.add_node("A".to_string());
        graph.add_node("B".to_string());

        assert_eq!(graph.nodes().len(), 2);
        assert_eq!(graph.edges().len(), 0);

        graph.add_edge(("A".to_string(), "B".to_string()));
        assert_eq!(graph.edges().len(), 1);
    }

    #[test]
    fn test_number_stream() {
        let mut stream = NumberStream::new(vec![1, 2, 3]);

        assert_eq!(stream.next().unwrap().unwrap(), 1);
        assert_eq!(stream.next().unwrap().unwrap(), 2);
        assert_eq!(stream.next().unwrap().unwrap(), 3);
        assert_eq!(stream.next().unwrap(), None);
    }

    #[test]
    fn test_sqlite_database() {
        let db = SqliteDatabase;

        let conn = db.connect().unwrap();
        assert_eq!(conn, "sqlite_connection");

        let mut conn_mut = conn;
        let transaction = db.begin_transaction(&mut conn_mut).unwrap();
        assert_eq!(transaction, "sqlite_transaction");

        assert!(db.commit(transaction).is_ok());
    }

    #[test]
    fn test_key_value_iterator() {
        let items = vec![
            ("key1".to_string(), "value1".to_string()),
            ("key2".to_string(), "value2".to_string()),
        ];

        let mut iterator = KeyValueIterator::new(items);

        assert_eq!(iterator.next(), Some("value1".to_string()));
        assert_eq!(iterator.next(), Some("value2".to_string()));
        assert_eq!(iterator.next(), None);
    }
}
