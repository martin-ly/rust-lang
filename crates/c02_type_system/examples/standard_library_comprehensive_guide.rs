//! 标准库全面指南示例
//!
//! 本示例全面展示Rust标准库的核心模块和最佳实践：
//! - std::collections - 集合类型深度使用
//! - std::iter - 迭代器模式
//! - std::fs/io - 文件系统操作
//! - std::sync - 并发原语
//! - std::time - 时间处理
//! - std::fmt - 格式化
//!
//! # 知识结构
//! ```text
//! 标准库全面指南
//! ├── 集合类型 (Collections)
//! │   ├── Vec - 动态数组
//! │   ├── HashMap - 哈希映射
//! │   ├── HashSet - 哈希集合
//! │   ├── BTreeMap - 有序映射
//! │   └── BinaryHeap - 优先队列
//! ├── 迭代器 (Iterator)
//! │   ├── 适配器方法
//! │   ├── 消费方法
//! │   └── 自定义迭代器
//! ├── 文件系统 (Filesystem)
//! │   ├── 文件读写
//! │   ├── 目录操作
//! │   └── 路径处理
//! └── 并发同步 (Sync)
//!     ├── Mutex/RwLock
//!     ├── Arc
//!     └── 原子类型
//! ```

#![allow(unused)]

use std::collections::{BTreeMap, BinaryHeap, HashMap, HashSet, VecDeque};
use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufRead, BufReader, BufWriter, Read, Write};
use std::iter::{self, FromIterator};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

/// # 集合类型深度示例
///
/// ## Vec - 动态数组的最佳实践
pub fn vec_comprehensive_examples() {
    println!("\n=== Vec 全面示例 ===\n");

    // 1. 创建方式对比
    // 方式1: new() - 推荐，清晰表达意图
    let mut v1: Vec<i32> = Vec::new();
    v1.push(1);
    v1.push(2);

    // 方式2: with_capacity() - 预知大小时使用，避免重新分配
    let mut v2 = Vec::with_capacity(1000);
    for i in 0..1000 {
        v2.push(i);
    }
    println!("Capacity: {}, Len: {}", v2.capacity(), v2.len());

    // 方式3: vec![] - 初始值已知时使用
    let v3 = vec![1, 2, 3, 4, 5];

    // 方式4: from_iter - 从迭代器创建
    let _v4: Vec<i32> = (0..10).collect();

    // 2. 高效操作
    // 批量添加，比单个push更高效
    let mut v5 = vec![1, 2, 3];
    v5.extend_from_slice(&[4, 5, 6]);

    // 保留内存，清空但不释放内存（性能优化）
    v5.clear();
    v5.push(1); // 重用已分配的内存

    // 3. 排序和搜索
    let mut nums = vec![3, 1, 4, 1, 5, 9, 2, 6];

    // 稳定排序
    nums.sort();
    println!("Sorted: {:?}", nums);

    // 自定义排序
    let mut words = vec!["apple", "Banana", "cherry", "Date"];
    words.sort_by(|a, b| a.to_lowercase().cmp(&b.to_lowercase()));
    println!("Case-insensitive sorted: {:?}", words);

    // 二分搜索（要求已排序）
    if let Ok(idx) = nums.binary_search(&5) {
        println!("Found 5 at index: {}", idx);
    }

    // 4. 内存管理技巧
    let mut large_vec = vec![0; 10000];
    large_vec.shrink_to_fit(); // 释放多余容量
    println!("After shrink: capacity = {}", large_vec.capacity());

    // 5. 不安全但高效的操作（谨慎使用）
    unsafe {
        let raw_ptr = v3.as_ptr();
        println!("First element via raw pointer: {}", *raw_ptr);
    }
}

/// ## HashMap - 哈希映射的最佳实践
pub fn hashmap_comprehensive_examples() {
    println!("\n=== HashMap 全面示例 ===\n");

    // 1. 创建和容量管理
    let mut map: HashMap<String, i32> = HashMap::with_capacity(100);
    map.reserve(50); // 预分配更多空间

    // 2. 插入模式
    // 模式1: 直接插入
    map.insert("key1".to_string(), 100);

    // 模式2: entry API - 更优雅的处理不存在的情况
    let value = map.entry("key2".to_string()).or_insert(200);
    *value += 1; // 可以修改
    println!("key2 value: {}", map.get("key2").unwrap());

    // 模式3: or_insert_with - 避免不必要的计算
    map.entry("key3".to_string())
        .or_insert_with(|| expensive_computation());

    // 3. 批量操作
    let keys = vec!["a", "b", "c"];
    let values = vec![1, 2, 3];
    let map2: HashMap<_, _> = keys.into_iter().zip(values).collect();
    println!("Map from zip: {:?}", map2);

    // 4. 迭代模式
    // 只遍历键
    for key in map.keys() {
        println!("Key: {}", key);
    }

    // 只遍历值
    let sum: i32 = map.values().sum();
    println!("Sum of values: {}", sum);

    // 遍历键值对（消耗map）
    for (key, value) in map {
        println!("{} => {}", key, value);
    }

    // 5. 高级用法：保留和过滤
    let mut scores: HashMap<String, i32> = [
        ("Alice".to_string(), 85),
        ("Bob".to_string(), 92),
        ("Carol".to_string(), 78),
    ]
    .into_iter()
    .collect();

    // 保留高分
    scores.retain(|_name, score| *score >= 80);
    println!("High scores: {:?}", scores);
}

fn expensive_computation() -> i32 {
    println!("Computing expensive value...");
    42
}

/// ## HashSet - 哈希集合的最佳实践
pub fn hashset_comprehensive_examples() {
    println!("\n=== HashSet 全面示例 ===\n");

    let mut set1: HashSet<i32> = HashSet::new();
    set1.insert(1);
    set1.insert(2);
    set1.insert(3);

    let set2: HashSet<i32> = [2, 3, 4, 5].into_iter().collect();

    // 集合运算
    println!("Union: {:?}", set1.union(&set2).collect::<Vec<_>>());
    println!(
        "Intersection: {:?}",
        set1.intersection(&set2).collect::<Vec<_>>()
    );
    println!(
        "Difference: {:?}",
        set1.difference(&set2).collect::<Vec<_>>()
    );
    println!(
        "Symmetric Difference: {:?}",
        set1.symmetric_difference(&set2).collect::<Vec<_>>()
    );

    // 判断子集和超集
    let subset: HashSet<i32> = [1, 2].into_iter().collect();
    println!("Is subset: {}", subset.is_subset(&set1));
    println!("Is superset: {}", set1.is_superset(&subset));

    // 去重实战：统计唯一单词
    let text = "the quick brown fox jumps over the lazy dog";
    let words: HashSet<_> = text.split_whitespace().collect();
    println!("Unique words: {:?}", words);
    println!("Word count: {}", words.len());
}

/// ## BTreeMap - 有序映射的最佳实践
pub fn btreemap_comprehensive_examples() {
    println!("\n=== BTreeMap 全面示例 ===\n");

    // BTreeMap保持键的有序性
    let mut map: BTreeMap<String, i32> = BTreeMap::new();
    map.insert("Charlie".to_string(), 30);
    map.insert("Alice".to_string(), 25);
    map.insert("Bob".to_string(), 35);

    // 遍历时自动按顺序
    println!("Sorted by key:");
    for (name, age) in &map {
        println!("  {}: {}", name, age);
    }

    // 范围查询（HashMap不支持）
    let range = map.range::<String, _>(String::from("Bob")..=String::from("Charlie"));
    println!("Range query:");
    for (name, age) in range {
        println!("  {}: {}", name, age);
    }

    // 获取最小/最大键（利用BTreeMap的有序性）
    if let Some((first_name, _)) = map.iter().next() {
        println!("First: {}", first_name);
    }
    if let Some((last_name, _)) = map.iter().next_back() {
        println!("Last: {}", last_name);
    }
}

/// ## BinaryHeap - 优先队列的最佳实践
pub fn binaryheap_comprehensive_examples() {
    println!("\n=== BinaryHeap 全面示例 ===\n");

    // 默认最大堆
    let mut max_heap = BinaryHeap::new();
    max_heap.push(3);
    max_heap.push(1);
    max_heap.push(4);
    max_heap.push(1);
    max_heap.push(5);

    println!("Max heap pop order:");
    while let Some(val) = max_heap.pop() {
        println!("  {}", val);
    }

    // 最小堆：使用Reverse包装器
    use std::cmp::Reverse;
    let mut min_heap = BinaryHeap::new();
    min_heap.push(Reverse(3));
    min_heap.push(Reverse(1));
    min_heap.push(Reverse(4));

    println!("Min heap pop order:");
    while let Some(Reverse(val)) = min_heap.pop() {
        println!("  {}", val);
    }

    // Top-K 问题实战
    let numbers = vec![7, 2, 9, 1, 5, 8, 3, 6, 4];
    let k = 3;
    let top_k = find_top_k(numbers, k);
    println!("Top {} numbers: {:?}", k, top_k);
}

fn find_top_k(nums: Vec<i32>, k: usize) -> Vec<i32> {
    use std::cmp::Reverse;
    let mut heap = BinaryHeap::with_capacity(k);

    for num in nums {
        if heap.len() < k {
            heap.push(Reverse(num));
        } else if let Some(&Reverse(min)) = heap.peek() {
            if num > min {
                heap.pop();
                heap.push(Reverse(num));
            }
        }
    }

    heap.into_sorted_vec().into_iter().map(|Reverse(x)| x).collect()
}

/// # 迭代器模式深度示例
pub fn iterator_comprehensive_examples() {
    println!("\n=== 迭代器全面示例 ===\n");

    let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // 1. 转换适配器
    let doubled: Vec<i32> = numbers.iter().map(|x| x * 2).collect();
    println!("Doubled: {:?}", doubled);

    // 2. 过滤
    let evens: Vec<&i32> = numbers.iter().filter(|&&x| x % 2 == 0).collect();
    println!("Evens: {:?}", evens);

    // 3. 复杂链式操作
    let result: i32 = numbers
        .iter()
        .filter(|&&x| x > 5) // 过滤大于5的
        .map(|x| x * x)      // 平方
        .take(2)             // 只取前2个
        .sum();              // 求和
    println!("Complex chain result: {}", result);

    // 4. 窗口和滑动
    let window_sums: Vec<i32> = numbers
        .windows(3)
        .map(|w| w.iter().sum())
        .collect();
    println!("Window sums: {:?}", window_sums);

    // 5. 分组
    let by_parity: HashMap<bool, Vec<i32>> = numbers
        .into_iter()
        .fold(HashMap::new(), |mut acc, x| {
            acc.entry(x % 2 == 0).or_default().push(x);
            acc
        });
    println!("By parity: {:?}", by_parity);

    // 6. 自定义迭代器
    let fib = Fibonacci::new().take(10);
    println!("First 10 Fibonacci: {:?}", fib.collect::<Vec<_>>());
}

// 自定义斐波那契迭代器
struct Fibonacci {
    curr: u64,
    next: u64,
}

impl Fibonacci {
    fn new() -> Self {
        Fibonacci { curr: 0, next: 1 }
    }
}

impl Iterator for Fibonacci {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.curr;
        self.curr = self.next;
        self.next = self.curr + current;
        Some(current)
    }
}

/// # 文件系统操作深度示例
pub fn filesystem_comprehensive_examples() -> io::Result<()> {
    println!("\n=== 文件系统全面示例 ===\n");

    // 1. 创建临时目录进行演示
    let temp_dir = std::env::temp_dir().join("rust_stdlib_examples");
    fs::create_dir_all(&temp_dir)?;

    // 2. 文件写入方式对比
    // 方式1: 一次性写入（小文件）
    let small_file = temp_dir.join("small.txt");
    fs::write(&small_file, "Hello, World!")?;

    // 方式2: 缓冲写入（大文件）
    let large_file = temp_dir.join("large.txt");
    {
        let file = File::create(&large_file)?;
        let mut writer = BufWriter::new(file);
        for i in 0..1000 {
            writeln!(writer, "Line {}", i)?;
        }
        // 缓冲自动刷新
    }

    // 方式3: 追加模式
    let append_file = temp_dir.join("append.txt");
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(&append_file)?;
    writeln!(file, "First line")?;
    writeln!(file, "Second line")?;

    // 3. 文件读取方式对比
    // 方式1: 一次性读取（小文件）
    let content = fs::read_to_string(&small_file)?;
    println!("Small file content: {}", content);

    // 方式2: 缓冲读取（大文件，逐行）
    let file = File::open(&large_file)?;
    let reader = BufReader::new(file);
    let mut line_count = 0;
    for line in reader.lines() {
        let _ = line?;
        line_count += 1;
        if line_count >= 5 {
            println!("... (truncated, total {} lines)", line_count);
            break;
        }
    }

    // 方式3: 分块读取（二进制文件）
    let mut file = File::open(&small_file)?;
    let mut buffer = [0u8; 1024];
    let bytes_read = file.read(&mut buffer)?;
    println!("Read {} bytes", bytes_read);

    // 4. 目录操作
    println!("\nDirectory entries:");
    for entry in fs::read_dir(&temp_dir)? {
        let entry = entry?;
        let metadata = entry.metadata()?;
        println!(
            "  {} ({} bytes)",
            entry.file_name().to_string_lossy(),
            metadata.len()
        );
    }

    // 5. 路径处理
    let path = Path::new("/usr/local/bin/rustc");
    println!("\nPath analysis:");
    println!("  File name: {:?}", path.file_name());
    println!("  Extension: {:?}", path.extension());
    println!("  Parent: {:?}", path.parent());
    println!("  Is absolute: {}", path.is_absolute());

    // 6. 构建路径
    let mut path_buf = PathBuf::from("/home/user");
    path_buf.push("projects");
    path_buf.push("myapp");
    path_buf.set_extension("toml");
    println!("  Built path: {:?}", path_buf);

    // 清理
    fs::remove_dir_all(&temp_dir)?;
    println!("\nCleaned up temp directory");

    Ok(())
}

/// # 并发同步原语深度示例
pub fn sync_comprehensive_examples() {
    println!("\n=== 同步原语全面示例 ===\n");

    use std::thread;

    // 1. Mutex - 互斥锁
    {
        let counter = Arc::new(Mutex::new(0));
        let mut handles = vec![];

        for _ in 0..10 {
            let counter = Arc::clone(&counter);
            let handle = thread::spawn(move || {
                let mut num = counter.lock().unwrap();
                *num += 1;
                // 锁在这里自动释放
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        println!("Counter result: {}", *counter.lock().unwrap());
    }

    // 2. RwLock - 读写锁（读多写少场景）
    {
        let data = Arc::new(RwLock::new(HashMap::new()));

        // 写操作
        {
            let mut write_guard = data.write().unwrap();
            write_guard.insert("key".to_string(), "value".to_string());
        } // 写锁释放

        // 多线程读操作
        let mut handles = vec![];
        for i in 0..5 {
            let data = Arc::clone(&data);
            handles.push(thread::spawn(move || {
                let read_guard = data.read().unwrap();
                println!("Reader {} got: {:?}", i, read_guard.get("key"));
            }));
        }

        for handle in handles {
            handle.join().unwrap();
        }
    }

    // 3. 使用模式：避免在锁内做耗时操作
    println!("\nMutex best practice:");
    let data = Arc::new(Mutex::new(vec![1, 2, 3, 4, 5]));
    {
        // BAD: 在锁内做耗时操作
        // let mut guard = data.lock().unwrap();
        // thread::sleep(Duration::from_secs(1)); // 阻塞其他线程
        // guard.push(6);

        // GOOD: 最小化临界区
        let new_value = {
            let guard = data.lock().unwrap();
            guard.iter().sum::<i32>() // 快速计算
        }; // 锁立即释放

        let mut guard = data.lock().unwrap();
        guard.push(new_value);
        println!("Added computed value: {}", new_value);
    }
}

/// # 时间处理深度示例
pub fn time_comprehensive_examples() {
    println!("\n=== 时间处理全面示例 ===\n");

    // 1. 测量代码执行时间
    let start = Instant::now();
    let mut sum = 0;
    for i in 0..1_000_000 {
        sum += i;
    }
    let duration = start.elapsed();
    println!("Sum {} computed in {:?}", sum, duration);

    // 2. 超时模式
    let operation_start = Instant::now();
    let timeout = Duration::from_millis(100);

    let mut count = 0;
    while operation_start.elapsed() < timeout {
        count += 1;
        if count > 1000 {
            break;
        }
    }
    println!("Completed {} iterations before timeout", count);

    // 3. Duration 运算
    let d1 = Duration::from_secs(60);
    let d2 = Duration::from_millis(500);
    let total = d1 + d2;
    println!("Total duration: {:?}", total);
    println!("In milliseconds: {}", total.as_millis());

    // 4. 比较和最小/最大
    let durations = vec![
        Duration::from_millis(100),
        Duration::from_millis(50),
        Duration::from_millis(200),
    ];
    let min_dur = durations.iter().min().unwrap();
    println!("Minimum duration: {:?}", min_dur);
}

/// # 格式化深度示例
pub fn fmt_comprehensive_examples() {
    println!("\n=== 格式化全面示例 ===\n");

    // 1. 数字格式化
    let num = 1234.5678;
    println!("Default: {}", num);
    println!("Precision 2: {:.2}", num);
    println!("Width 10: {:10}", num);
    println!("Width 10, precision 2: {:10.2}", num);
    println!("Left align: {:<10.2}", num);
    println!("Zero pad: {:010.2}", num);

    // 2. 整数格式化
    let n = 255;
    println!("\nDecimal: {}", n);
    println!("Hex: {:x}", n);
    println!("Hex upper: {:X}", n);
    println!("Octal: {:o}", n);
    println!("Binary: {:b}", n);

    // 3. 自定义类型的格式化
    let point = Point { x: 3.5, y: 4.2 };
    println!("\nDisplay: {}", point);
    println!("Debug: {:?}", point);
    println!("Pretty debug: {:#?}", point);

    // 4. 格式化到字符串
    let formatted = format!("Point: {}", point);
    println!("Formatted string: {}", formatted);
}

#[derive(Debug)]
struct Point {
    x: f64,
    y: f64,
}

impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({:.2}, {:.2})", self.x, self.y)
    }
}

/// # 错误处理模式示例
pub fn error_handling_examples() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== 错误处理模式示例 ===\n");

    // 1. 使用 ? 运算符传播错误
    let content = std::fs::read_to_string("nonexistent.txt")
        .map_err(|e| format!("Failed to read file: {}", e))?;
    println!("Content: {}", content);

    Ok(())
}

fn main() {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║     Rust 标准库全面指南示例                               ║");
    println!("╚══════════════════════════════════════════════════════════╝");

    vec_comprehensive_examples();
    hashmap_comprehensive_examples();
    hashset_comprehensive_examples();
    btreemap_comprehensive_examples();
    binaryheap_comprehensive_examples();
    iterator_comprehensive_examples();

    if let Err(e) = filesystem_comprehensive_examples() {
        eprintln!("Filesystem example error: {}", e);
    }

    sync_comprehensive_examples();
    time_comprehensive_examples();
    fmt_comprehensive_examples();

    if let Err(e) = error_handling_examples() {
        println!("Expected error (file not found): {}", e);
    }

    println!("\n✅ 所有标准库示例完成!");
}
