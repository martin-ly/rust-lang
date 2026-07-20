# 🦀 Rust实用代码示例


## 📊 目录

- [🦀 Rust实用代码示例](#-rust实用代码示例)
  - [📊 目录](#-目录)
  - [📋 示例概述](#-示例概述)
  - [🎯 基础示例](#-基础示例)
    - [字符串处理](#字符串处理)
      - [字符串拼接](#字符串拼接)
      - [字符串分割和过滤](#字符串分割和过滤)
    - [文件操作](#文件操作)
      - [读取文件内容](#读取文件内容)
      - [写入文件](#写入文件)
  - [🔢 数据处理示例](#-数据处理示例)
    - [数值计算](#数值计算)
      - [统计计算](#统计计算)
      - [数组操作](#数组操作)
    - [集合操作](#集合操作)
      - [HashMap使用](#hashmap使用)
  - [🌐 网络编程示例](#-网络编程示例)
    - [HTTP客户端](#http客户端)
      - [简单的HTTP请求](#简单的http请求)
      - [JSON处理](#json处理)
  - [🔄 并发编程示例](#-并发编程示例)
    - [线程池](#线程池)
      - [简单的线程池实现](#简单的线程池实现)
    - [异步编程](#异步编程)
      - [异步文件处理](#异步文件处理)
  - [🗃️ 数据库操作示例](#️-数据库操作示例)
    - [SQLite操作](#sqlite操作)
      - [基本的CRUD操作](#基本的crud操作)
  - [🎮 游戏开发示例](#-游戏开发示例)
    - [简单的游戏循环](#简单的游戏循环)
      - [基础游戏结构](#基础游戏结构)
  - [🧪 测试示例](#-测试示例)
    - [单元测试](#单元测试)
      - [完整的测试套件](#完整的测试套件)
  - [📞 使用建议](#-使用建议)
    - [学习建议](#学习建议)
    - [实践建议](#实践建议)


**创建时间**: 2025年9月25日 13:45
**版本**: v1.0
**适用对象**: Rust初学者到中级开发者

---

## 📋 示例概述

本文档提供了Rust语言的实际应用示例，涵盖常见编程场景和最佳实践。这些示例可以帮助您更好地理解Rust的特性和用法。

---

## 🎯 基础示例

### 字符串处理

#### 字符串拼接

```rust
// ✅ 高效的字符串拼接
fn build_greeting(name: &str) -> String {
    let mut greeting = String::with_capacity(name.len() + 13);
    greeting.push_str("Hello, ");
    greeting.push_str(name);
    greeting.push_str("!");
    greeting
}

// 使用示例
fn main() {
    let name = "Alice";
    let greeting = build_greeting(name);
    println!("{}", greeting);
}
```

#### 字符串分割和过滤

```rust
use std::collections::HashSet;

fn process_text(text: &str) -> Vec<String> {
    text.split_whitespace()
        .filter(|word| word.len() > 3)
        .map(|word| word.to_lowercase())
        .collect()
}

fn find_unique_words(text: &str) -> HashSet<String> {
    text.split_whitespace()
        .map(|word| word.to_lowercase())
        .collect()
}
```

### 文件操作

#### 读取文件内容

```rust
use std::fs;
use std::io;

fn read_file_content(path: &str) -> Result<String, io::Error> {
    fs::read_to_string(path)
}

fn read_file_lines(path: &str) -> Result<Vec<String>, io::Error> {
    let content = fs::read_to_string(path)?;
    Ok(content.lines().map(|line| line.to_string()).collect())
}

// 使用示例
fn main() -> Result<(), io::Error> {
    let content = read_file_content("example.txt")?;
    println!("文件内容: {}", content);
    Ok(())
}
```

#### 写入文件

```rust
use std::fs;
use std::io;

fn write_to_file(path: &str, content: &str) -> Result<(), io::Error> {
    fs::write(path, content)
}

fn append_to_file(path: &str, content: &str) -> Result<(), io::Error> {
    use std::fs::OpenOptions;
    use std::io::Write;

    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)?;

    writeln!(file, "{}", content)?;
    Ok(())
}
```

---

## 🔢 数据处理示例

### 数值计算

#### 统计计算

```rust
#[derive(Debug)]
struct Statistics {
    sum: f64,
    average: f64,
    min: f64,
    max: f64,
}

impl Statistics {
    fn new(data: &[f64]) -> Option<Self> {
        if data.is_empty() {
            return None;
        }

        let sum: f64 = data.iter().sum();
        let average = sum / data.len() as f64;
        let min = data.iter().fold(f64::INFINITY, |a, &b| a.min(b));
        let max = data.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));

        Some(Statistics {
            sum,
            average,
            min,
            max,
        })
    }
}

// 使用示例
fn main() {
    let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
    if let Some(stats) = Statistics::new(&data) {
        println!("统计结果: {:?}", stats);
    }
}
```

#### 数组操作

```rust
fn find_duplicates<T: Eq + std::hash::Hash + Clone>(items: &[T]) -> Vec<T> {
    use std::collections::HashSet;

    let mut seen = HashSet::new();
    let mut duplicates = Vec::new();

    for item in items {
        if !seen.insert(item) {
            duplicates.push(item.clone());
        }
    }

    duplicates
}

fn merge_sorted_arrays<T: Ord + Clone>(arr1: &[T], arr2: &[T]) -> Vec<T> {
    let mut result = Vec::with_capacity(arr1.len() + arr2.len());
    let mut i = 0;
    let mut j = 0;

    while i < arr1.len() && j < arr2.len() {
        if arr1[i] <= arr2[j] {
            result.push(arr1[i].clone());
            i += 1;
        } else {
            result.push(arr2[j].clone());
            j += 1;
        }
    }

    result.extend_from_slice(&arr1[i..]);
    result.extend_from_slice(&arr2[j..]);

    result
}
```

### 集合操作

#### HashMap使用

```rust
use std::collections::HashMap;

fn count_words(text: &str) -> HashMap<String, usize> {
    text.split_whitespace()
        .fold(HashMap::new(), |mut acc, word| {
            let word = word.to_lowercase();
            *acc.entry(word).or_insert(0) += 1;
            acc
        })
}

fn group_by<T, K, F>(items: Vec<T>, key_fn: F) -> HashMap<K, Vec<T>>
where
    K: std::hash::Hash + Eq,
    F: Fn(&T) -> K,
{
    items.into_iter()
        .fold(HashMap::new(), |mut acc, item| {
            let key = key_fn(&item);
            acc.entry(key).or_insert_with(Vec::new).push(item);
            acc
        })
}

// 使用示例
fn main() {
    let text = "hello world hello rust world";
    let word_count = count_words(text);
    println!("单词计数: {:?}", word_count);
}
```

---

## 🌐 网络编程示例

### HTTP客户端

#### 简单的HTTP请求

```rust
use std::io::Read;

fn make_http_request(url: &str) -> Result<String, Box<dyn std::error::Error>> {
    let response = ureq::get(url).call()?;
    let mut body = String::new();
    response.into_reader().read_to_string(&mut body)?;
    Ok(body)
}

// 异步版本
async fn make_async_http_request(url: &str) -> Result<String, Box<dyn std::error::Error>> {
    let response = reqwest::get(url).await?;
    let body = response.text().await?;
    Ok(body)
}
```

#### JSON处理

```rust
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct User {
    id: u32,
    name: String,
    email: String,
}

#[derive(Serialize, Deserialize)]
struct ApiResponse {
    users: Vec<User>,
    total: u32,
}

fn parse_json_response(json: &str) -> Result<ApiResponse, serde_json::Error> {
    serde_json::from_str(json)
}

fn create_json_response(users: Vec<User>) -> String {
    let response = ApiResponse {
        total: users.len() as u32,
        users,
    };
    serde_json::to_string_pretty(&response).unwrap()
}
```

---

## 🔄 并发编程示例

### 线程池

#### 简单的线程池实现

```rust
use std::sync::{Arc, Mutex};
use std::thread;
use std::sync::mpsc;

type Job = Box<dyn FnOnce() + Send + 'static>;

struct ThreadPool {
    workers: Vec<Worker>,
    sender: mpsc::Sender<Job>,
}

impl ThreadPool {
    fn new(size: usize) -> Self {
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        ThreadPool { workers, sender }
    }

    fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.send(job).unwrap();
    }
}

struct Worker {
    id: usize,
    thread: thread::JoinHandle<()>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Job>>>) -> Self {
        let thread = thread::spawn(move || {
            while let Ok(job) = receiver.lock().unwrap().recv() {
                job();
            }
        });

        Worker { id, thread }
    }
}
```

### 异步编程

#### 异步文件处理

```rust
use tokio::fs;
use tokio::io::AsyncReadExt;

async fn process_file_async(path: &str) -> Result<String, Box<dyn std::error::Error>> {
    let mut file = fs::File::open(path).await?;
    let mut contents = String::new();
    file.read_to_string(&mut contents).await?;

    // 模拟异步处理
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    Ok(contents.to_uppercase())
}

async fn process_multiple_files(paths: Vec<&str>) -> Vec<Result<String, Box<dyn std::error::Error>>> {
    let handles: Vec<_> = paths.into_iter()
        .map(|path| tokio::spawn(process_file_async(path)))
        .collect();

    let mut results = Vec::new();
    for handle in handles {
        results.push(handle.await.unwrap());
    }

    results
}
```

---

## 🗃️ 数据库操作示例

### SQLite操作

#### 基本的CRUD操作

```rust
use rusqlite::{Connection, Result, params};

#[derive(Debug)]
struct User {
    id: i32,
    name: String,
    email: String,
}

struct UserRepository {
    conn: Connection,
}

impl UserRepository {
    fn new(db_path: &str) -> Result<Self> {
        let conn = Connection::open(db_path)?;
        conn.execute(
            "CREATE TABLE IF NOT EXISTS users (
                id INTEGER PRIMARY KEY,
                name TEXT NOT NULL,
                email TEXT NOT NULL UNIQUE
            )",
            [],
        )?;

        Ok(UserRepository { conn })
    }

    fn create_user(&self, name: &str, email: &str) -> Result<i32> {
        self.conn.execute(
            "INSERT INTO users (name, email) VALUES (?1, ?2)",
            params![name, email],
        )?;

        Ok(self.conn.last_insert_rowid() as i32)
    }

    fn get_user(&self, id: i32) -> Result<User> {
        let mut stmt = self.conn.prepare("SELECT id, name, email FROM users WHERE id = ?1")?;
        let user = stmt.query_row(params![id], |row| {
            Ok(User {
                id: row.get(0)?,
                name: row.get(1)?,
                email: row.get(2)?,
            })
        })?;

        Ok(user)
    }

    fn update_user(&self, id: i32, name: &str, email: &str) -> Result<()> {
        self.conn.execute(
            "UPDATE users SET name = ?1, email = ?2 WHERE id = ?3",
            params![name, email, id],
        )?;

        Ok(())
    }

    fn delete_user(&self, id: i32) -> Result<()> {
        self.conn.execute(
            "DELETE FROM users WHERE id = ?1",
            params![id],
        )?;

        Ok(())
    }

    fn list_users(&self) -> Result<Vec<User>> {
        let mut stmt = self.conn.prepare("SELECT id, name, email FROM users")?;
        let user_iter = stmt.query_map([], |row| {
            Ok(User {
                id: row.get(0)?,
                name: row.get(1)?,
                email: row.get(2)?,
            })
        })?;

        let mut users = Vec::new();
        for user in user_iter {
            users.push(user?);
        }

        Ok(users)
    }
}
```

---

## 🎮 游戏开发示例

### 简单的游戏循环

#### 基础游戏结构

```rust
use std::time::{Duration, Instant};

trait GameObject {
    fn update(&mut self, delta_time: f32);
    fn render(&self);
}

struct Game {
    objects: Vec<Box<dyn GameObject>>,
    running: bool,
}

impl Game {
    fn new() -> Self {
        Game {
            objects: Vec::new(),
            running: true,
        }
    }

    fn add_object(&mut self, obj: Box<dyn GameObject>) {
        self.objects.push(obj);
    }

    fn run(&mut self) {
        let mut last_time = Instant::now();

        while self.running {
            let current_time = Instant::now();
            let delta_time = (current_time - last_time).as_secs_f32();
            last_time = current_time;

            self.update(delta_time);
            self.render();

            // 控制帧率
            std::thread::sleep(Duration::from_millis(16)); // ~60 FPS
        }
    }

    fn update(&mut self, delta_time: f32) {
        for obj in &mut self.objects {
            obj.update(delta_time);
        }
    }

    fn render(&self) {
        for obj in &self.objects {
            obj.render();
        }
    }

    fn quit(&mut self) {
        self.running = false;
    }
}

// 示例游戏对象
struct Player {
    x: f32,
    y: f32,
    speed: f32,
}

impl GameObject for Player {
    fn update(&mut self, delta_time: f32) {
        // 简单的移动逻辑
        self.x += self.speed * delta_time;
    }

    fn render(&self) {
        println!("Player at ({:.1}, {:.1})", self.x, self.y);
    }
}
```

---

## 🧪 测试示例

### 单元测试

#### 完整的测试套件

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_statistics_calculation() {
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let stats = Statistics::new(&data).unwrap();

        assert_eq!(stats.sum, 15.0);
        assert_eq!(stats.average, 3.0);
        assert_eq!(stats.min, 1.0);
        assert_eq!(stats.max, 5.0);
    }

    #[test]
    fn test_statistics_empty_data() {
        let data: Vec<f64> = vec![];
        let stats = Statistics::new(&data);

        assert!(stats.is_none());
    }

    #[test]
    fn test_word_counting() {
        let text = "hello world hello rust world";
        let word_count = count_words(text);

        assert_eq!(word_count.get("hello"), Some(&2));
        assert_eq!(word_count.get("world"), Some(&2));
        assert_eq!(word_count.get("rust"), Some(&1));
    }

    #[test]
    fn test_find_duplicates() {
        let items = vec![1, 2, 3, 2, 4, 3, 5];
        let duplicates = find_duplicates(&items);

        assert_eq!(duplicates.len(), 2);
        assert!(duplicates.contains(&2));
        assert!(duplicates.contains(&3));
    }

    #[test]
    fn test_merge_sorted_arrays() {
        let arr1 = vec![1, 3, 5];
        let arr2 = vec![2, 4, 6];
        let merged = merge_sorted_arrays(&arr1, &arr2);

        assert_eq!(merged, vec![1, 2, 3, 4, 5, 6]);
    }
}

// 集成测试
#[cfg(test)]
mod integration_tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_user_repository_operations() {
        let temp_dir = tempdir().unwrap();
        let db_path = temp_dir.path().join("test.db");

        let repo = UserRepository::new(db_path.to_str().unwrap()).unwrap();

        // 测试创建用户
        let user_id = repo.create_user("Alice", "alice@example.com").unwrap();
        assert!(user_id > 0);

        // 测试获取用户
        let user = repo.get_user(user_id).unwrap();
        assert_eq!(user.name, "Alice");
        assert_eq!(user.email, "alice@example.com");

        // 测试更新用户
        repo.update_user(user_id, "Alice Smith", "alice.smith@example.com").unwrap();
        let updated_user = repo.get_user(user_id).unwrap();
        assert_eq!(updated_user.name, "Alice Smith");

        // 测试删除用户
        repo.delete_user(user_id).unwrap();
        assert!(repo.get_user(user_id).is_err());
    }
}
```

---

## 📞 使用建议

### 学习建议

1. **从简单开始**: 先理解基础示例，再学习复杂示例
2. **动手实践**: 运行示例代码，修改参数观察结果
3. **逐步扩展**: 在示例基础上添加自己的功能
4. **阅读文档**: 结合官方文档理解API用法

### 实践建议

1. **项目应用**: 在实际项目中使用这些示例
2. **性能测试**: 测试示例的性能表现
3. **错误处理**: 添加适当的错误处理
4. **代码审查**: 定期审查和改进代码

---

**示例状态**: 🔄 持续更新中
**最后更新**: 2025年9月25日 13:45
**适用版本**: Rust 1.70+

---

*本示例文档提供了Rust的实际应用示例，帮助您更好地理解和使用Rust语言。如有任何问题或建议，欢迎反馈。*
