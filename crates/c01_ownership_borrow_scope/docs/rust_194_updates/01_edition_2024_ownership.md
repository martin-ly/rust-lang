# Rust 1.94 + Edition 2024: 所有权系统深度解析

> **Rust 版本**: 1.94.0
> **Edition**: 2024
> **最后更新**: 2026-03-10
> **文档级别**: Tier 1 - 核心基础

---

## 目录

- [Rust 1.94 + Edition 2024: 所有权系统深度解析](#rust-194--edition-2024-所有权系统深度解析)
  - [目录](#目录)
  - [Edition 2024 所有权新特性](#edition-2024-所有权新特性)
    - [1.1 精确捕获语法 `use<..>`](#11-精确捕获语法-use)
    - [1.2 闭包类型推断增强](#12-闭包类型推断增强)
  - [智能指针改进](#智能指针改进)
    - [2.1 RefCell 映射 API (稳定)](#21-refcell-映射-api-稳定)
    - [2.2 Box::new\_uninit 与 MaybeUninit 集成](#22-boxnew_uninit-与-maybeuninit-集成)
  - [内存布局优化](#内存布局优化)
    - [3.1 Edition 2024 内存对齐改进](#31-edition-2024-内存对齐改进)
    - [3.2 零成本抽象验证](#32-零成本抽象验证)
  - [MaybeUninit 最佳实践](#maybeuninit-最佳实践)
    - [4.1 安全初始化模式](#41-安全初始化模式)
    - [4.2 与标准库集成](#42-与标准库集成)
  - [实战示例](#实战示例)
    - [5.1 高性能对象池](#51-高性能对象池)
    - [5.2 线程安全的细粒度锁](#52-线程安全的细粒度锁)
  - [相关文档](#相关文档)

---

## Edition 2024 所有权新特性

### 1.1 精确捕获语法 `use<..>`

Edition 2024 引入了 `use<..>` 语法，用于精确控制闭包捕获的变量：

```rust
// Edition 2024
fn process_data(data: Vec<i32>) -> impl Iterator<Item = i32> + use<> {
    // use<> 表示不捕获任何外部变量
    data.into_iter().filter(|x| x % 2 == 0)
}

fn with_capture(data: Vec<i32>) -> impl FnOnce() -> Vec<i32> + use<data> {
    // use<data> 明确表示只捕获 data
    move || {
        println!("Processing {} items", data.len());
        data
    }
}
```

**优势**:

- 明确的捕获语义
- 更好的错误信息
- 避免意外的环境捕获

### 1.2 闭包类型推断增强

```rust
// Rust 1.94 改进的闭包类型推断
let numbers = vec![1, 2, 3, 4, 5];

// 编译器现在能更好地推断复杂闭包类型
let sum: i32 = numbers.iter()
    .filter(|&&x| x > 2)  // 自动推断 &i32
    .map(|&x| x * 2)      // 自动推断 i32 -> i32
    .sum();
```

---

## 智能指针改进

### 2.1 RefCell 映射 API (稳定)

Rust 1.94 完善了 `Ref::map` 和 `RefMut::map`，允许在不克隆的情况下访问嵌套数据：

```rust
use std::cell::{RefCell, Ref, RefMut};

#[derive(Debug)]
struct AppConfig {
    database: DatabaseConfig,
    server: ServerConfig,
}

#[derive(Debug)]
struct DatabaseConfig {
    url: String,
    pool_size: usize,
}

#[derive(Debug)]
struct ServerConfig {
    host: String,
    port: u16,
}

fn main() {
    let config = RefCell::new(AppConfig {
        database: DatabaseConfig {
            url: "postgres://localhost".to_string(),
            pool_size: 10,
        },
        server: ServerConfig {
            host: "0.0.0.0".to_string(),
            port: 8080,
        },
    });

    // 使用 Ref::map 只借用 database 字段
    let db_config: Ref<DatabaseConfig> = Ref::map(
        config.borrow(),
        |c| &c.database
    );
    println!("Database URL: {}", db_config.url);
    // db_config 在这里释放，config 的其他字段可以可变借用

    // 使用 RefMut::map 可变借用 server 字段
    let mut server_config: RefMut<ServerConfig> = RefMut::map(
        config.borrow_mut(),
        |c| &mut c.server
    );
    server_config.port = 3000;
    println!("New port: {}", server_config.port);
}
```

**适用场景**:

- 大型配置结构的部分访问
- 避免不必要的克隆
- 细粒度的内部可变性

### 2.2 Box::new_uninit 与 MaybeUninit 集成

```rust
use std::alloc::{alloc, Layout};
use std::mem::MaybeUninit;
use std::ptr::NonNull;

/// 使用 MaybeUninit 创建未初始化 Box
fn create_uninit_box<T>() -> Box<MaybeUninit<T>> {
    let layout = Layout::new::<T>();
    unsafe {
        let ptr = alloc(layout) as *mut MaybeUninit<T>;
        assert!(!ptr.is_null(), "Allocation failed");
        Box::from_raw(ptr)
    }
}

/// 安全初始化后转换为 Box<T>
fn init_box<T>(uninit: Box<MaybeUninit<T>>, value: T) -> Box<T> {
    let ptr = Box::into_raw(uninit);
    unsafe {
        (*ptr).write(value);
        // SAFETY: 我们已经初始化了值
        Box::from_raw(ptr as *mut T)
    }
}
```

---

## 内存布局优化

### 3.1 Edition 2024 内存对齐改进

```rust
// 使用 repr(C) 和 align 进行精确内存控制
#[repr(C, align(64))]  // 64字节对齐，适合缓存行
pub struct CacheLineAligned<T> {
    value: T,
    // 填充到64字节
    _padding: [u8; 64 - std::mem::size_of::<T>()],
}

impl<T> CacheLineAligned<T> {
    pub fn new(value: T) -> Self {
        assert!(std::mem::size_of::<T>() <= 64);
        Self {
            value,
            _padding: [0; 64 - std::mem::size_of::<T>()],
        }
    }

    pub fn get(&self) -> &T {
        &self.value
    }

    pub fn get_mut(&mut self) -> &mut T {
        &mut self.value
    }
}
```

### 3.2 零成本抽象验证

```rust
// Rust 1.94 确保零成本抽象的编译器优化
pub fn optimized_filter_map() {
    let numbers: Vec<i32> = (0..1000).collect();

    // 这个迭代器链在 release 模式下会被优化为高效循环
    let sum: i32 = numbers
        .into_iter()
        .filter(|x| x % 2 == 0)
        .map(|x| x * x)
        .take(100)
        .sum();

    println!("Sum: {}", sum);
}

// 编译器 Explorer (godbolt.org) 验证：
// 生成的汇编代码与手写循环相当
```

---

## MaybeUninit 最佳实践

### 4.1 安全初始化模式

```rust
use std::mem::{self, MaybeUninit};

/// 安全地初始化数组，避免 unsafe 代码直接暴露
pub struct SafeArray<T, const N: usize> {
    data: [MaybeUninit<T>; N],
    initialized: usize,
}

impl<T, const N: usize> SafeArray<T, N> {
    pub fn new() -> Self {
        // SAFETY: MaybeUninit 不需要初始化
        let data = unsafe { MaybeUninit::uninit().assume_init() };
        Self {
            data,
            initialized: 0,
        }
    }

    pub fn push(&mut self, value: T) -> Result<(), T> {
        if self.initialized >= N {
            return Err(value);
        }
        self.data[self.initialized].write(value);
        self.initialized += 1;
        Ok(())
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.initialized {
            // SAFETY: 我们知道这个索引已初始化
            Some(unsafe { self.data[index].assume_init_ref() })
        } else {
            None
        }
    }

    pub fn into_array(mut self) -> Result<[T; N], Self> {
        if self.initialized == N {
            // SAFETY: 所有元素都已初始化
            let array = unsafe { mem::transmute_copy(&self.data) };
            mem::forget(self); // 防止 drop 运行
            Ok(array)
        } else {
            Err(self)
        }
    }
}

impl<T, const N: usize> Drop for SafeArray<T, N> {
    fn drop(&mut self) {
        // 只释放已初始化的元素
        for i in 0..self.initialized {
            unsafe {
                self.data[i].assume_init_drop();
            }
        }
    }
}
```

### 4.2 与标准库集成

```rust
use std::io::{self, Read};

/// 使用 MaybeUninit 进行高效的 IO 读取
pub fn read_exact_uninit<R: Read>(reader: &mut R, buf: &mut [MaybeUninit<u8>]) -> io::Result<()> {
    let mut total_read = 0;

    while total_read < buf.len() {
        // SAFETY: MaybeUninit 可以安全地持有未初始化内存
        let slice = unsafe {
            std::slice::from_raw_parts_mut(
                buf.as_mut_ptr().add(total_read) as *mut u8,
                buf.len() - total_read
            )
        };

        match reader.read(slice) {
            Ok(0) => return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "Unexpected EOF"
            )),
            Ok(n) => total_read += n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        }
    }

    Ok(())
}
```

---

## 实战示例

### 5.1 高性能对象池

```rust
use std::cell::RefCell;
use std::mem::MaybeUninit;

/// Edition 2024 优化的高性能对象池
pub struct ObjectPool<T, const N: usize> {
    storage: RefCell<[MaybeUninit<T>; N]>,
    available: RefCell<Vec<usize>>, // 可用索引
}

impl<T, const N: usize> ObjectPool<T, N> {
    pub fn new<F>(init: F) -> Self
    where
        F: Fn() -> T,
    {
        let storage = unsafe { MaybeUninit::uninit().assume_init() };
        let available: Vec<usize> = (0..N).collect();

        let pool = Self {
            storage: RefCell::new(storage),
            available: RefCell::new(available),
        };

        // 初始化所有对象
        for i in 0..N {
            pool.storage.borrow_mut()[i].write(init());
        }

        pool
    }

    pub fn acquire(&self) -> Option<PooledObject<T, N>> {
        let idx = self.available.borrow_mut().pop()?;
        Some(PooledObject {
            pool: self,
            index: idx,
        })
    }

    fn release(&self, index: usize) {
        self.available.borrow_mut().push(index);
    }
}

pub struct PooledObject<'a, T, const N: usize> {
    pool: &'a ObjectPool<T, N>,
    index: usize,
}

impl<'a, T, const N: usize> std::ops::Deref for PooledObject<'a, T, N> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { self.pool.storage.borrow()[self.index].assume_init_ref() }
    }
}

impl<'a, T, const N: usize> std::ops::DerefMut for PooledObject<'a, T, N> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.pool.storage.borrow_mut()[self.index].assume_init_mut() }
    }
}

impl<'a, T, const N: usize> Drop for PooledObject<'a, T, N> {
    fn drop(&mut self) {
        self.pool.release(self.index);
    }
}

// 使用示例
fn main() {
    let pool: ObjectPool<Vec<u8>, 100> = ObjectPool::new(|| Vec::with_capacity(1024));

    {
        let mut obj = pool.acquire().unwrap();
        obj.extend_from_slice(b"Hello, World!");
        // obj 在这里自动释放回池中
    }

    // 可以重新获取
    let obj2 = pool.acquire().unwrap();
    assert!(obj2.capacity() >= 1024);
}
```

### 5.2 线程安全的细粒度锁

```rust
use std::cell::{RefCell, Ref, RefMut};
use std::sync::Mutex;

/// 使用 RefCell 映射实现细粒度锁定
pub struct FineGrainedCache<K, V> {
    buckets: Vec<Mutex<RefCell<Vec<(K, V)>>>>,
}

impl<K: Eq + std::hash::Hash, V> FineGrainedCache<K, V> {
    pub fn new(bucket_count: usize) -> Self {
        let mut buckets = Vec::with_capacity(bucket_count);
        for _ in 0..bucket_count {
            buckets.push(Mutex::new(RefCell::new(Vec::new())));
        }
        Self { buckets }
    }

    fn get_bucket_index(&self, key: &K) -> usize {
        use std::hash::{DefaultHasher, Hash, Hasher};
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        (hasher.finish() as usize) % self.buckets.len()
    }

    pub fn get(&self, key: &K) -> Option<Ref<V>> {
        let bucket_idx = self.get_bucket_index(key);
        let bucket = self.buckets[bucket_idx].lock().ok()?;

        Ref::filter_map(bucket.borrow(), |vec| {
            vec.iter().find(|(k, _)| k == key).map(|(_, v)| v)
        }).ok()
    }

    pub fn insert(&self, key: K, value: V) {
        let bucket_idx = self.get_bucket_index(key);
        let bucket = self.buckets[bucket_idx].lock().unwrap();

        let mut vec = bucket.borrow_mut();
        if let Some(pos) = vec.iter().position(|(k, _)| k == &key) {
            vec[pos] = (key, value);
        } else {
            vec.push((key, value));
        }
    }
}
```

---

## 相关文档

- [Rust 1.94 发布说明](../../../docs/06_toolchain/16_rust_1.94_release_notes.md)
- [Edition 2024 指南](../../../docs/05_guides/RUST_194_MIGRATION_GUIDE.md)
- [MaybeUninit 文档](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html)
- [RefCell 映射 API](https://doc.rust-lang.org/std/cell/struct.Ref.html#method.map)
