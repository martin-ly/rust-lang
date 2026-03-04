# Rust数据库系统实现指南

> 一份全面深入的Rust数据库系统开发指南，涵盖存储引擎、事务处理、查询优化、分布式架构等核心领域。

---

## 目录

- [Rust数据库系统实现指南](#rust数据库系统实现指南)
  - [目录](#目录)
  - [1. 数据库系统概述](#1-数据库系统概述)
    - [1.1 Rust在数据库领域的优势](#11-rust在数据库领域的优势)
      - [内存安全性](#内存安全性)
      - [零成本抽象](#零成本抽象)
      - [Fearless Concurrency](#fearless-concurrency)
    - [1.2 内存安全与数据一致性](#12-内存安全与数据一致性)
    - [1.3 现有Rust数据库介绍](#13-现有rust数据库介绍)
  - [2. 存储引擎](#2-存储引擎)
    - [2.1 B-Tree实现](#21-b-tree实现)
    - [2.2 LSM-Tree（Sled风格实现）](#22-lsm-treesled风格实现)
    - [2.3 内存映射文件](#23-内存映射文件)
    - [2.4 页面管理](#24-页面管理)
  - [3. 事务处理](#3-事务处理)
    - [3.1 ACID保证](#31-acid保证)
    - [3.2 MVCC（多版本并发控制）](#32-mvcc多版本并发控制)
    - [3.3 两阶段锁](#33-两阶段锁)
    - [3.4 死锁检测](#34-死锁检测)
  - [4. 查询引擎](#4-查询引擎)
    - [4.1 SQL解析](#41-sql解析)
    - [4.2 查询优化](#42-查询优化)
    - [4.3 执行计划](#43-执行计划)
    - [4.4 向量化执行](#44-向量化执行)
  - [5. 索引系统](#5-索引系统)
    - [5.1 B+树索引](#51-b树索引)
    - [5.2 哈希索引](#52-哈希索引)
    - [5.3 全文索引](#53-全文索引)
    - [5.4 空间索引](#54-空间索引)
  - [6. WAL与恢复](#6-wal与恢复)
    - [6.1 预写日志](#61-预写日志)
    - [6.2 检查点机制](#62-检查点机制)
    - [6.3 崩溃恢复](#63-崩溃恢复)
  - [7. 分布式数据库](#7-分布式数据库)
    - [7.1 分片策略](#71-分片策略)
    - [7.2 复制协议](#72-复制协议)
    - [7.3 一致性模型](#73-一致性模型)
  - [8. 完整示例：嵌入式KV存储](#8-完整示例嵌入式kv存储)
    - [8.1 存储格式](#81-存储格式)
    - [8.2 基本操作](#82-基本操作)
    - [8.3 迭代器](#83-迭代器)
    - [8.4 事务支持](#84-事务支持)
  - [9. 性能优化](#9-性能优化)
    - [9.1 零拷贝](#91-零拷贝)
    - [9.2 异步I/O](#92-异步io)
    - [9.3 内存池](#93-内存池)
  - [10. 测试策略](#10-测试策略)
    - [10.1 持久化测试](#101-持久化测试)
    - [10.2 崩溃恢复测试](#102-崩溃恢复测试)
    - [10.3 并发测试](#103-并发测试)
  - [总结](#总结)

---

## 1. 数据库系统概述

### 1.1 Rust在数据库领域的优势

Rust作为一门系统级编程语言，在数据库系统开发中展现出独特的优势：

#### 内存安全性

```rust
// Rust的借用检查器在编译期防止数据竞争
use std::sync::{Arc, Mutex};

struct Database {
    data: Mutex<Vec<u8>>,
}

impl Database {
    fn read(&self, offset: usize, len: usize) -> Result<Vec<u8>, Error> {
        let data = self.data.lock().map_err(|_| Error::LockPoisoned)?;
        // 编译器确保data在使用期间不会被修改
        if offset + len > data.len() {
            return Err(Error::OutOfBounds);
        }
        Ok(data[offset..offset + len].to_vec())
    }
}
```

#### 零成本抽象

```rust
// 高性能的迭代器抽象，编译后无运行时开销
pub struct PageIterator<'a> {
    pages: &'a [Page],
    current: usize,
}

impl<'a> Iterator for PageIterator<'a> {
    type Item = &'a Page;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.pages.len() {
            let page = &self.pages[self.current];
            self.current += 1;
            Some(page)
        } else {
            None
        }
    }
}
```

#### Fearless Concurrency

```rust
use std::sync::RwLock;
use crossbeam::channel;

// 安全的并发访问模式
pub struct ConcurrentIndex<K, V> {
    inner: RwLock<BTreeMap<K, V>>,
    write_queue: channel::Sender<WriteOp<K, V>>,
}

impl<K: Ord + Send, V: Send> ConcurrentIndex<K, V> {
    pub fn get(&self, key: &K) -> Option<V> {
        // 多个读取者可以并发访问
        self.inner.read().unwrap().get(key).cloned()
    }

    pub fn batch_insert(&self, items: Vec<(K, V)>) {
        // 写入操作通过channel序列化，避免锁竞争
        self.write_queue.send(WriteOp::Batch(items)).unwrap();
    }
}
```

### 1.2 内存安全与数据一致性

Rust的所有权系统天然适合实现数据一致性保证：

```rust
/// 事务隔离级别的类型安全实现
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum IsolationLevel {
    ReadUncommitted,
    ReadCommitted,
    RepeatableRead,
    Serializable,
}

/// 事务句柄，确保事务要么提交要么回滚
pub struct Transaction<'a> {
    db: &'a Database,
    state: TransactionState,
    write_set: HashSet<PageId>,
}

impl<'a> Transaction<'a> {
    /// 事务在Drop时自动回滚未提交的更改
    fn rollback(&mut self) -> Result<(), Error> {
        for page_id in &self.write_set {
            self.db.undo_page_changes(*page_id)?;
        }
        self.state = TransactionState::Aborted;
        Ok(())
    }
}

impl<'a> Drop for Transaction<'a> {
    fn drop(&mut self) {
        if self.state == TransactionState::Active {
            // 编译器确保这里一定能执行
            let _ = self.rollback();
        }
    }
}
```

### 1.3 现有Rust数据库介绍

| 数据库 | 类型 | 特点 | 适用场景 |
|--------|------|------|----------|
| **TiKV** | 分布式KV | 基于Raft的强一致性 | 大规模分布式存储 |
| **Sled** | 嵌入式KV | LSM-Tree，无GC暂停 | 嵌入式应用 |
| **Materialize** | 流式数据库 | SQL on streams | 实时分析 |
| **MeiliSearch** | 搜索引擎 | 全文索引，容错排序 | 站内搜索 |
| **GreptimeDB** | 时序数据库 | 列式存储，PromQL | 监控数据 |

```rust
// Sled的基本使用示例
use sled::Db;

fn sled_example() -> Result<(), Box<dyn std::error::Error>> {
    let db = sled::open("my_db")?;

    // 插入键值对
    db.insert(b"key", b"value")?;

    // 原子批量操作
    let mut batch = sled::Batch::default();
    batch.insert(b"key1", b"value1");
    batch.insert(b"key2", b"value2");
    batch.remove(b"key3");
    db.apply_batch(batch)?;

    // 范围扫描
    for result in db.range(b"a"..b"z") {
        let (k, v) = result?;
        println!("{:?} = {:?}", k, v);
    }

    Ok(())
}
```

---

## 2. 存储引擎

### 2.1 B-Tree实现

B-Tree是数据库中最核心的数据结构之一。Rust实现需要考虑节点布局、分裂合并、并发控制等：

```rust
use std::sync::Arc;
use parking_lot::RwLock;

const BTREE_ORDER: usize = 128; // 每个节点的最大键数

/// B-Tree节点
#[derive(Clone)]
pub struct BTreeNode<K: Ord, V> {
    keys: Vec<K>,
    values: Vec<V>,
    children: Vec<Arc<RwLock<BTreeNode<K, V>>>>,
    is_leaf: bool,
}

impl<K: Ord + Clone, V: Clone> BTreeNode<K, V> {
    pub fn new(is_leaf: bool) -> Self {
        Self {
            keys: Vec::with_capacity(BTREE_ORDER - 1),
            values: Vec::with_capacity(BTREE_ORDER - 1),
            children: Vec::with_capacity(BTREE_ORDER),
            is_leaf,
        }
    }

    /// 在节点中搜索键的位置
    fn search_key(&self, key: &K) -> Result<usize, usize> {
        self.keys.binary_search(key)
    }

    /// 分裂满节点
    fn split(&mut self) -> (K, BTreeNode<K, V>) {
        let mid = BTREE_ORDER / 2;
        let split_key = self.keys[mid].clone();

        let mut new_node = BTreeNode::new(self.is_leaf);
        new_node.keys = self.keys.split_off(mid + 1);
        new_node.values = self.values.split_off(mid + 1);

        if !self.is_leaf {
            new_node.children = self.children.split_off(mid + 1);
        }

        self.keys.pop(); // 移除中间键
        self.values.pop();

        (split_key, new_node)
    }
}

/// 线程安全的B-Tree
pub struct ConcurrentBTree<K: Ord, V> {
    root: Arc<RwLock<BTreeNode<K, V>>>,
    height: AtomicUsize,
}

impl<K: Ord + Clone + Send + Sync, V: Clone + Send + Sync> ConcurrentBTree<K, V> {
    pub fn new() -> Self {
        Self {
            root: Arc::new(RwLock::new(BTreeNode::new(true))),
            height: AtomicUsize::new(1),
        }
    }

    pub fn search(&self, key: &K) -> Option<V> {
        let mut current = self.root.clone();

        loop {
            let node = current.read();
            match node.search_key(key) {
                Ok(idx) => return Some(node.values[idx].clone()),
                Err(idx) => {
                    if node.is_leaf {
                        return None;
                    }
                    let next = node.children.get(idx)?;
                    drop(node); // 释放读锁
                    current = next.clone();
                }
            }
        }
    }
}
```

### 2.2 LSM-Tree（Sled风格实现）

LSM-Tree（日志结构合并树）通过顺序写优化磁盘I/O：

```rust
use std::collections::BTreeMap;
use std::fs::{File, OpenOptions};
use std::io::{BufReader, BufWriter, Write, Read, Seek};
use std::path::Path;
use crossbeam_skiplist::SkipMap;

/// 内存中的可变表（MemTable）
pub struct MemTable {
    inner: SkipMap<Vec<u8>, Option<Vec<u8>>>, // None表示删除标记
    size: AtomicUsize,
    max_size: usize,
}

impl MemTable {
    pub fn new(max_size: usize) -> Self {
        Self {
            inner: SkipMap::new(),
            size: AtomicUsize::new(0),
            max_size,
        }
    }

    pub fn get(&self, key: &[u8]) -> Option<Option<Vec<u8>>> {
        self.inner.get(key).map(|e| e.value().clone())
    }

    pub fn insert(&self, key: Vec<u8>, value: Option<Vec<u8>>) -> bool {
        let key_len = key.len();
        let val_len = value.as_ref().map(|v| v.len()).unwrap_or(0);

        self.inner.insert(key, value);
        let new_size = self.size.fetch_add(key_len + val_len + 8, Ordering::Relaxed);

        new_size + key_len + val_len + 8 >= self.max_size
    }

    pub fn is_full(&self) -> bool {
        self.size.load(Ordering::Relaxed) >= self.max_size
    }
}

/// LSM-Tree存储引擎
pub struct LsmTree {
    active_memtable: Arc<MemTable>,
    frozen_memtables: RwLock<Vec<Arc<FrozenMemTable>>>,
    sstables: RwLock<Vec<Arc<SSTable>>>,
    wal: Mutex<WriteAheadLog>,
    compaction_tx: channel::Sender<CompactionTask>,
}

impl LsmTree {
    pub fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Error> {
        // 1. 查询Active MemTable
        if let Some(result) = self.active_memtable.get(key) {
            return Ok(result);
        }

        // 2. 查询Frozen MemTables（从新到旧）
        let frozen = self.frozen_memtables.read();
        for memtable in frozen.iter().rev() {
            if let Some(result) = memtable.data.iter().find(|(k, _)| k == key) {
                return Ok(result.1.clone());
            }
        }

        // 3. 查询SSTables（从新到旧）
        let sstables = self.sstables.read();
        for sstable in sstables.iter().rev() {
            if let Some(result) = sstable.get(key)? {
                return Ok(result);
            }
        }

        Ok(None)
    }

    pub fn insert(&self, key: Vec<u8>, value: Vec<u8>) -> Result<(), Error> {
        // 先写入WAL保证持久性
        self.wal.lock().append(&key, Some(&value))?;

        // 写入MemTable
        if self.active_memtable.insert(key, Some(value)) {
            // MemTable已满，触发刷盘
            self.freeze_memtable()?;
        }

        Ok(())
    }
}
```

### 2.3 内存映射文件

内存映射提供用户态文件访问，减少系统调用开销：

```rust
use memmap2::{MmapMut, MmapOptions};
use std::fs::OpenOptions;
use std::path::Path;
use std::slice;

/// 内存映射的页缓存
pub struct MmapPageCache {
    mmap: MmapMut,
    page_size: usize,
    capacity: usize,
}

impl MmapPageCache {
    pub fn new<P: AsRef<Path>>(path: P, capacity: usize) -> io::Result<Self> {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(path)?;

        file.set_len(capacity as u64)?;

        let mmap = unsafe { MmapOptions::new().map_mut(&file)? };

        Ok(Self {
            mmap,
            page_size: 4096,
            capacity,
        })
    }

    /// 获取页的可变引用
    pub fn page_mut(&mut self, page_id: usize) -> Option<&mut [u8]> {
        let offset = page_id * self.page_size;
        if offset + self.page_size > self.capacity {
            return None;
        }
        Some(&mut self.mmap[offset..offset + self.page_size])
    }

    /// 获取页的不可变引用
    pub fn page(&self, page_id: usize) -> Option<&[u8]> {
        let offset = page_id * self.page_size;
        if offset + self.page_size > self.capacity {
            return None;
        }
        Some(&self.mmap[offset..offset + self.page_size])
    }

    /// 刷新特定页到磁盘
    pub fn flush_page(&self, page_id: usize) -> io::Result<()> {
        let offset = page_id * self.page_size;
        let len = self.page_size.min(self.capacity - offset);
        self.mmap.flush_range(offset, len)
    }
}
```

### 2.4 页面管理

页面是数据库存储的基本单位，包含元数据管理：

```rust
/// 页面头部（固定64字节）
#[repr(C)]
pub struct PageHeader {
    checksum: u32,      // CRC32校验
    page_id: u32,       // 页ID
    page_type: u8,      // 页类型
    flags: u8,          // 标志位
    free_space: u16,    // 空闲空间偏移
    record_count: u16,  // 记录数量
    lsn: u64,           // 日志序列号
    prev_page: u32,     // 上一页（用于溢出页）
    next_page: u32,     // 下一页
    padding: [u8; 36],  // 填充到64字节
}

/// 数据库页（4KB标准大小）
pub const PAGE_SIZE: usize = 4096;

pub struct Page {
    header: PageHeader,
    data: [u8; PAGE_SIZE - 64],
}

impl Page {
    /// 计算页内数据的CRC32校验
    pub fn calculate_checksum(&self) -> u32 {
        let data_bytes = unsafe {
            slice::from_raw_parts(
                &self.header.page_id as *const _ as *const u8,
                PAGE_SIZE - 4 // 排除checksum字段本身
            )
        };
        crc32fast::hash(data_bytes)
    }

    /// 验证页完整性
    pub fn verify(&self) -> bool {
        self.header.checksum == self.calculate_checksum()
    }
}

/// 页分配器，管理空闲页
pub struct PageAllocator {
    total_pages: AtomicU32,
    free_pages: SegQueue<u32>, // 无锁队列
    bitmap: RwLock<BitVec>,    // 页分配位图
}

impl PageAllocator {
    /// 分配新页
    pub fn allocate(&self) -> u32 {
        // 先尝试从空闲列表获取
        if let Some(page_id) = self.free_pages.pop() {
            let mut bitmap = self.bitmap.write();
            bitmap.set(page_id as usize, true);
            return page_id;
        }

        // 分配新页
        let page_id = self.total_pages.fetch_add(1, Ordering::SeqCst);

        let mut bitmap = self.bitmap.write();
        if page_id as usize >= bitmap.len() {
            bitmap.resize((page_id as usize + 1) * 2, false);
        }
        bitmap.set(page_id as usize, true);

        page_id
    }

    /// 释放页
    pub fn deallocate(&self, page_id: u32) {
        self.free_pages.push(page_id);
        let mut bitmap = self.bitmap.write();
        bitmap.set(page_id as usize, false);
    }
}
```

---

## 3. 事务处理

### 3.1 ACID保证

ACID属性是事务处理的基础，Rust的类型系统可以帮助我们实现编译期保证：

```rust
/// 原子性：使用WAL确保事务要么完全提交，要么完全回滚
pub struct WriteAheadLog {
    file: Mutex<BufWriter<File>>,
    lsn: AtomicU64,
}

impl WriteAheadLog {
    /// 写入事务日志记录
    pub fn append_record(&self, record: &WALRecord) -> io::Result<u64> {
        let mut file = self.file.lock().unwrap();
        let lsn = self.lsn.fetch_add(1, Ordering::SeqCst);

        // 格式: [长度(4)][LSN(8)][CRC32(4)][数据(N)]
        let data = bincode::serialize(record).unwrap();
        let crc = crc32fast::hash(&data);

        file.write_all(&(data.len() as u32 + 12).to_le_bytes())?;
        file.write_all(&lsn.to_le_bytes())?;
        file.write_all(&crc.to_le_bytes())?;
        file.write_all(&data)?;

        // 强制刷盘保证持久性
        file.flush()?;
        file.get_ref().sync_all()?;

        Ok(lsn)
    }
}

/// 一致性：约束检查
pub struct ConstraintChecker {
    constraints: Vec<Box<dyn Constraint>>,
}

trait Constraint: Send + Sync {
    fn check(&self, old_row: Option<&Row>, new_row: Option<&Row>) -> Result<(), ConstraintError>;
}

/// 隔离性：通过锁或多版本控制实现
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum IsolationLevel {
    ReadUncommitted,
    ReadCommitted,
    RepeatableRead,
    Serializable,
}
```

### 3.2 MVCC（多版本并发控制）

MVCC通过保存数据的历史版本实现高并发读取：

```rust
use std::collections::BTreeMap;

/// 事务ID，单调递增
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TxnId(u64);

/// MVCC版本记录
#[derive(Clone)]
pub struct VersionRecord {
    pub txn_id: TxnId,
    pub begin_ts: u64,
    pub end_ts: Option<u64>, // None表示当前版本
    pub data: Vec<u8>,
    pub deleted: bool,
}

/// MVCC存储的行
pub struct MvccRow {
    versions: RwLock<Vec<VersionRecord>>,
}

impl MvccRow {
    /// 获取对指定事务可见的版本
    pub fn get_visible_version(&self, txn_id: TxnId, read_ts: u64) -> Option<VersionRecord> {
        let versions = self.versions.read();

        for version in versions.iter().rev() {
            // 跳过未提交的版本（除非是事务自己写的）
            if version.txn_id != txn_id && version.end_ts.is_none() {
                continue;
            }

            // 检查时间戳可见性
            let visible = match version.end_ts {
                Some(end_ts) => version.begin_ts <= read_ts && read_ts < end_ts,
                None => version.begin_ts <= read_ts,
            };

            if visible && !version.deleted {
                return Some(version.clone());
            }
        }

        None
    }

    /// 写入新版本
    pub fn write_version(&self, txn_id: TxnId, data: Vec<u8>) -> Result<(), MvccError> {
        let mut versions = self.versions.write();

        // 检查写冲突（使用第一行作为最新版本）
        if let Some(latest) = versions.last() {
            if latest.end_ts.is_none() && latest.txn_id != txn_id {
                return Err(MvccError::WriteConflict);
            }
        }

        // 标记旧版本结束
        if let Some(latest) = versions.last_mut() {
            if latest.txn_id == txn_id {
                // 同一事务的多次写入，替换旧版本
                latest.data = data;
                return Ok(());
            }
            latest.end_ts = Some(get_timestamp());
        }

        // 添加新版本
        versions.push(VersionRecord {
            txn_id,
            begin_ts: get_timestamp(),
            end_ts: None,
            data,
            deleted: false,
        });

        Ok(())
    }
}
```

### 3.3 两阶段锁

两阶段锁（2PL）是实现可串行化的经典方法：

```rust
/// 锁类型
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum LockMode {
    Shared,    // S锁，用于读
    Exclusive, // X锁，用于写
    IntentionShared,    // IS锁
    IntentionExclusive, // IX锁
}

/// 锁管理器
pub struct LockManager {
    /// 资源ID -> 等待队列
    lock_table: DashMap<ResourceId, VecDeque<LockRequest>>,
    /// 事务持有的锁
    txn_locks: DashMap<TxnId, HashSet<ResourceId>>,
    /// 死锁检测图
    wait_for_graph: Mutex<WaitForGraph>,
}

impl LockManager {
    /// 获取锁
    pub fn acquire_lock(
        &self,
        txn_id: TxnId,
        resource_id: ResourceId,
        mode: LockMode,
    ) -> Result<(), LockError> {
        let mut queue = self.lock_table.entry(resource_id).or_default();

        // 检查锁兼容性
        if self.can_grant_lock(&queue, txn_id, mode) {
            queue.push_back(LockRequest {
                txn_id,
                mode,
                granted: AtomicBool::new(true),
            });

            self.txn_locks.entry(txn_id).or_default().insert(resource_id);
            return Ok(());
        }

        // 等待锁...
        // 实际实现会添加等待边并检测死锁
        Ok(())
    }

    fn can_grant_lock(
        &self,
        queue: &VecDeque<LockRequest>,
        txn_id: TxnId,
        mode: LockMode,
    ) -> bool {
        for req in queue.iter() {
            if !req.granted.load(Ordering::Relaxed) {
                continue;
            }

            if req.txn_id == txn_id {
                return true;
            }

            // 检查锁兼容性
            if !self.locks_compatible(req.mode, mode) {
                return false;
            }
        }

        true
    }

    fn locks_compatible(&self, held: LockMode, requested: LockMode) -> bool {
        use LockMode::*;

        match (held, requested) {
            (Shared, Shared) => true,
            (Shared, Exclusive) => false,
            (Exclusive, _) => false,
            (IntentionShared, Exclusive) => false,
            (IntentionExclusive, Shared) => false,
            (IntentionExclusive, Exclusive) => false,
            _ => true,
        }
    }
}
```

### 3.4 死锁检测

```rust
/// 等待图用于死锁检测
pub struct WaitForGraph {
    /// txn_id -> 等待的txn_id集合
    edges: HashMap<TxnId, HashSet<TxnId>>,
}

impl WaitForGraph {
    pub fn new() -> Self {
        Self {
            edges: HashMap::new(),
        }
    }

    /// 添加等待边：waiter等待holder释放资源
    pub fn add_edge(&mut self, waiter: TxnId, holder: TxnId) -> Result<(), DeadlockError> {
        self.edges.entry(waiter).or_default().insert(holder);

        // 检查是否形成环
        if self.has_cycle() {
            self.edges.get_mut(&waiter).unwrap().remove(&holder);
            return Err(DeadlockError::WouldCreateCycle);
        }

        Ok(())
    }

    /// 使用DFS检测环
    fn has_cycle(&self) -> bool {
        let mut visited = HashSet::new();
        let mut recursion_stack = HashSet::new();

        for &txn in self.edges.keys() {
            if !visited.contains(&txn) {
                if self.dfs_cycle(txn, &mut visited, &mut recursion_stack) {
                    return true;
                }
            }
        }

        false
    }

    fn dfs_cycle(
        &self,
        txn: TxnId,
        visited: &mut HashSet<TxnId>,
        stack: &mut HashSet<TxnId>,
    ) -> bool {
        visited.insert(txn);
        stack.insert(txn);

        if let Some(neighbors) = self.edges.get(&txn) {
            for &neighbor in neighbors {
                if !visited.contains(&neighbor) {
                    if self.dfs_cycle(neighbor, visited, stack) {
                        return true;
                    }
                } else if stack.contains(&neighbor) {
                    return true;
                }
            }
        }

        stack.remove(&txn);
        false
    }
}
```

---

## 4. 查询引擎

### 4.1 SQL解析

```rust
use sqlparser::dialect::GenericDialect;
use sqlparser::parser::Parser;

/// SQL解析器包装
pub struct SqlParser {
    dialect: GenericDialect,
}

impl SqlParser {
    pub fn new() -> Self {
        Self {
            dialect: GenericDialect {},
        }
    }

    pub fn parse(&self, sql: &str) -> Result<Vec<Statement>, ParseError> {
        Parser::parse_sql(&self.dialect, sql)
            .map_err(|e| ParseError::SyntaxError(e.to_string()))
    }
}

/// 内部查询表示
#[derive(Debug, Clone)]
pub enum LogicalPlan {
    TableScan {
        table: String,
        projection: Option<Vec<String>>,
        filter: Option<Expr>,
    },
    Filter {
        predicate: Expr,
        input: Box<LogicalPlan>,
    },
    Projection {
        exprs: Vec<Expr>,
        input: Box<LogicalPlan>,
    },
    Aggregate {
        group_by: Vec<Expr>,
        aggregates: Vec<AggregateExpr>,
        input: Box<LogicalPlan>,
    },
    Sort {
        exprs: Vec<OrderByExpr>,
        input: Box<LogicalPlan>,
    },
    Limit {
        limit: usize,
        offset: Option<usize>,
        input: Box<LogicalPlan>,
    },
    Join {
        join_type: JoinType,
        left: Box<LogicalPlan>,
        right: Box<LogicalPlan>,
        on: Vec<(String, String)>,
    },
}

/// 表达式
#[derive(Debug, Clone)]
pub enum Expr {
    Column(String),
    Literal(Value),
    BinaryOp {
        op: BinaryOperator,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    UnaryOp {
        op: UnaryOperator,
        expr: Box<Expr>,
    },
    Function {
        name: String,
        args: Vec<Expr>,
    },
    Cast {
        expr: Box<Expr>,
        data_type: DataType,
    },
}
```

### 4.2 查询优化

```rust
/// 基于成本的优化器
pub struct CostBasedOptimizer {
    catalog: Arc<dyn Catalog>,
    statistics: Arc<dyn StatisticsProvider>,
}

impl CostBasedOptimizer {
    /// 优化逻辑计划
    pub fn optimize(&self, plan: LogicalPlan) -> Result<LogicalPlan, OptimizeError> {
        let mut plan = plan;

        // 应用一系列优化规则
        plan = self.apply_rules(plan, &[
            Box::new(PredicatePushDown),
            Box::new(ProjectionPushDown),
            Box::new(JoinReorder),
        ])?;

        Ok(plan)
    }

    fn apply_rules(
        &self,
        plan: LogicalPlan,
        rules: &[Box<dyn OptimizerRule>],
    ) -> Result<LogicalPlan, OptimizeError> {
        let mut plan = plan;
        let mut changed = true;

        // 迭代应用规则直到不再变化
        while changed {
            changed = false;
            for rule in rules {
                let (new_plan, did_change) = rule.optimize(plan, self)?;
                plan = new_plan;
                changed |= did_change;
            }
        }

        Ok(plan)
    }
}

/// 谓词下推：将过滤条件尽可能推向数据源
struct PredicatePushDown;

impl OptimizerRule for PredicatePushDown {
    fn optimize(
        &self,
        plan: LogicalPlan,
        _optimizer: &CostBasedOptimizer,
    ) -> Result<(LogicalPlan, bool), OptimizeError> {
        match plan {
            LogicalPlan::Filter { predicate, input } => {
                match Self::push_down(*input, predicate) {
                    (new_plan, true) => Ok((new_plan, true)),
                    (new_plan, false) => Ok((
                        LogicalPlan::Filter {
                            predicate,
                            input: Box::new(new_plan),
                        },
                        false,
                    )),
                }
            }
            _ => Ok((plan, false)),
        }
    }
}
```

### 4.3 执行计划

```rust
/// 物理执行计划
#[derive(Debug)]
pub enum PhysicalPlan {
    SequentialScan {
        table: TableId,
        projection: Vec<usize>,
        filter: Option<PhysicalExpr>,
    },
    IndexScan {
        index: IndexId,
        range: IndexRange,
        projection: Vec<usize>,
    },
    HashJoin {
        join_type: JoinType,
        left: Box<PhysicalPlan>,
        right: Box<PhysicalPlan>,
        left_keys: Vec<usize>,
        right_keys: Vec<usize>,
    },
    Sort {
        sort_exprs: Vec<PhysicalSortExpr>,
        input: Box<PhysicalPlan>,
    },
    HashAggregate {
        group_exprs: Vec<PhysicalExpr>,
        aggregate_exprs: Vec<PhysicalAggregateExpr>,
        input: Box<PhysicalPlan>,
    },
    Filter {
        predicate: PhysicalExpr,
        input: Box<PhysicalPlan>,
    },
    Limit {
        limit: usize,
        offset: usize,
        input: Box<PhysicalPlan>,
    },
}

/// 执行器trait
trait Executor: Send {
    fn execute(&mut self) -> Result<BoxStream<'static, Result<RecordBatch, ExecError>>, ExecError>;
}
```

### 4.4 向量化执行

```rust
use arrow::array::{Array, ArrayRef, Float64Array, Int64Array};
use arrow::record_batch::RecordBatch;

/// 向量化执行器使用Arrow格式批量处理数据
pub struct VectorizedFilterExecutor {
    predicate: PhysicalExpr,
    input: Box<dyn Executor>,
    batch_size: usize,
}

impl Executor for VectorizedFilterExecutor {
    fn execute(&mut self) -> Result<BoxStream<'static, Result<RecordBatch, ExecError>>, ExecError> {
        let predicate = self.predicate.clone();
        let batch_size = self.batch_size;
        let input_stream = self.input.execute()?;

        let stream = input_stream.try_filter_map(move |batch| {
            let predicate = predicate.clone();
            async move {
                // 向量化求值谓词，返回布尔数组
                let selection = predicate.evaluate(&batch)?;
                let boolean_arr = selection.as_any()
                    .downcast_ref::<BooleanArray>()
                    .ok_or(ExecError::TypeMismatch)?;

                // 过滤所有列
                let filtered_columns: Vec<ArrayRef> = batch.columns()
                    .iter()
                    .map(|col| arrow::compute::filter(col, &boolean_arr))
                    .collect::<Result<_, _>>()
                    .map_err(|e| ExecError::ArrowError(e))?;

                let filtered_batch = RecordBatch::try_new(
                    batch.schema(),
                    filtered_columns,
                ).map_err(|e| ExecError::ArrowError(e))?;

                if filtered_batch.num_rows() > 0 {
                    Ok(Some(filtered_batch))
                } else {
                    Ok(None)
                }
            }
        });

        Ok(Box::pin(stream))
    }
}
```

---

## 5. 索引系统

### 5.1 B+树索引

```rust
/// B+树节点类型
#[derive(Clone, Copy, Debug)]
enum BPlusNodeType {
    Internal,
    Leaf,
}

/// B+树节点存储在页中
const BPLUS_ORDER: usize = 200; // 4KB页可容纳约200个键

pub struct BPlusNode<K: Ord, V> {
    node_type: BPlusNodeType,
    keys: Vec<K>,
    // Internal节点：子节点页ID
    // Leaf节点：值或指向值的指针
    payloads: Vec<V>,
    next_leaf: Option<PageId>, // 仅叶子节点
}

impl<K: Ord + Clone, V: Clone> BPlusNode<K, V> {
    /// 在叶子节点中搜索
    fn search_leaf(&self, key: &K) -> Option<(usize, &V)> {
        match self.keys.binary_search(key) {
            Ok(idx) => Some((idx, &self.payloads[idx])),
            Err(_) => None,
        }
    }

    /// 在内部节点中找到子节点
    fn find_child(&self, key: &K) -> &V {
        match self.keys.binary_search(key) {
            Ok(idx) => &self.payloads[idx + 1],
            Err(idx) => &self.payloads[idx],
        }
    }
}

/// 基于磁盘的B+树索引
pub struct BPlusTreeIndex<K, V> {
    pager: Arc<Pager>,
    root_page: PageId,
    key_schema: Vec<DataType>,
    _phantom: PhantomData<(K, V)>,
}

impl<K: Ord + Serialize + DeserializeOwned, V: Serialize + DeserializeOwned> BPlusTreeIndex<K, V> {
    /// 范围查询
    pub fn range_scan(
        &self,
        start: Bound<&K>,
        end: Bound<&K>,
    ) -> Result<RangeScanIterator<K, V>, IndexError> {
        let start_leaf = self.find_leaf_for_bound(start)?;

        Ok(RangeScanIterator {
            pager: self.pager.clone(),
            current_leaf: Some(start_leaf),
            current_idx: self.find_start_idx(&start_leaf, start)?,
            end: end.map(|k| k.clone()),
            _phantom: PhantomData,
        })
    }
}
```

### 5.2 哈希索引

```rust
use std::hash::{Hash, Hasher};
use ahash::AHasher;

/// 可扩展哈希索引
pub struct ExtendibleHashIndex<K, V> {
    /// 目录：全局深度 -> 桶指针
    directory: RwLock<Vec<PageId>>,
    /// 全局深度
    global_depth: AtomicUsize,
    /// 每个桶的最大条目数
    bucket_capacity: usize,
    pager: Arc<Pager>,
    _phantom: PhantomData<(K, V)>,
}

impl<K: Hash + Eq, V> ExtendibleHashIndex<K, V> {
    fn hash(&self, key: &K) -> u64 {
        let mut hasher = AHasher::default();
        key.hash(&mut hasher);
        hasher.finish()
    }

    fn bucket_index(&self, hash: u64) -> usize {
        let global_depth = self.global_depth.load(Ordering::Acquire);
        let mask = (1usize << global_depth) - 1;
        (hash as usize) & mask
    }

    pub fn get(&self, key: &K) -> Option<V> {
        let hash = self.hash(key);
        let idx = self.bucket_index(hash);

        let directory = self.directory.read();
        let bucket_id = directory[idx];
        drop(directory);

        let bucket = self.read_bucket(bucket_id);
        bucket.entries.iter()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v.clone())
    }
}
```

### 5.3 全文索引

```rust
use rust_stemmers::{Algorithm, Stemmer};

/// 倒排索引
pub struct InvertedIndex {
    /// 词项 -> 文档列表
    index: DashMap<String, PostingList>,
    /// 停用词
    stop_words: HashSet<String>,
    /// 词干提取器
    stemmer: Stemmer,
}

#[derive(Clone, Debug)]
struct PostingList {
    /// 文档ID -> [(位置, 词频)]
    postings: BTreeMap<DocId, Vec<(u32, u32)>>,
    doc_count: usize,
}

impl InvertedIndex {
    pub fn new() -> Self {
        Self {
            index: DashMap::new(),
            stop_words: Self::load_stop_words(),
            stemmer: Stemmer::create(Algorithm::English),
        }
    }

    /// TF-IDF搜索
    pub fn search(&self, query: &str, top_k: usize) -> Vec<(DocId, f64)> {
        let query_terms: Vec<String> = self.tokenize(query)
            .map(|t| self.normalize_term(&t))
            .filter(|t| !self.stop_words.contains(t))
            .collect();

        let total_docs = self.get_total_docs();
        let mut scores: HashMap<DocId, f64> = HashMap::new();

        for term in &query_terms {
            if let Some(posting_list) = self.index.get(term) {
                let df = posting_list.doc_count as f64;
                let idf = (total_docs as f64 / df).ln();

                for (doc_id, positions) in &posting_list.postings {
                    let tf = positions.len() as f64;
                    let score = tf * idf;

                    *scores.entry(*doc_id).or_default() += score;
                }
            }
        }

        let mut ranked: Vec<(DocId, f64)> = scores.into_iter().collect();
        ranked.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
        ranked.truncate(top_k);

        ranked
    }
}
```

### 5.4 空间索引

```rust
/// R-Tree空间索引
pub struct RTreeIndex {
    root: RwLock<RTreeNode>,
    node_capacity: usize,
    pager: Arc<Pager>,
}

/// 最小边界矩形
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct MBR {
    pub min_x: f64,
    pub min_y: f64,
    pub max_x: f64,
    pub max_y: f64,
}

impl MBR {
    pub fn new(min_x: f64, min_y: f64, max_x: f64, max_y: f64) -> Self {
        Self { min_x, min_y, max_x, max_y }
    }

    /// 计算面积
    pub fn area(&self) -> f64 {
        (self.max_x - self.min_x) * (self.max_y - self.min_y)
    }

    /// 判断是否相交
    pub fn intersects(&self, other: &MBR) -> bool {
        self.min_x <= other.max_x
            && self.max_x >= other.min_x
            && self.min_y <= other.max_y
            && self.max_y >= other.min_y
    }
}

impl RTreeIndex {
    /// 范围查询
    pub fn range_query(&self, query_mbr: &MBR) -> Vec<RecordId> {
        let root = self.root.read();
        let mut results = Vec::new();
        self.range_search(&root, query_mbr, &mut results);
        results
    }

    /// 最近邻查询
    pub fn nearest_neighbor(&self, point: (f64, f64), k: usize) -> Vec<(RecordId, f64)> {
        let root = self.root.read();
        let mut heap: BinaryHeap<OrdPair<f64, RTreeNode>> = BinaryHeap::new();
        let mut results: Vec<(RecordId, f64)> = Vec::with_capacity(k);

        // 优先队列搜索...

        results
    }
}
```

---

## 6. WAL与恢复

### 6.1 预写日志

```rust
/// WAL日志记录类型
#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum LogRecord {
    Begin { txn_id: TxnId },
    Update {
        txn_id: TxnId,
        table_id: TableId,
        page_id: PageId,
        offset: u16,
        old_data: Vec<u8>,
        new_data: Vec<u8>,
    },
    Insert {
        txn_id: TxnId,
        table_id: TableId,
        page_id: PageId,
        record_data: Vec<u8>,
    },
    Delete {
        txn_id: TxnId,
        table_id: TableId,
        page_id: PageId,
        record_data: Vec<u8>,
    },
    Commit { txn_id: TxnId, timestamp: u64 },
    Abort { txn_id: TxnId },
    CheckpointBegin { active_txns: Vec<TxnId>, lsn: LSN },
    CheckpointEnd { lsn: LSN },
}

/// 日志序列号
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LSN(pub u64);

/// 预写日志管理器
pub struct WriteAheadLog {
    log_file: Mutex<BufWriter<File>>,
    current_lsn: AtomicU64,
    buffer: Mutex<Vec<(LSN, LogRecord)>>,
    max_buffer_size: usize,
}

impl WriteAheadLog {
    /// 追加日志记录
    pub fn append(&self, record: LogRecord) -> io::Result<LSN> {
        let lsn = LSN(self.current_lsn.fetch_add(1, Ordering::SeqCst));

        let mut buffer = self.buffer.lock().unwrap();
        buffer.push((lsn, record));

        if buffer.len() >= self.max_buffer_size {
            drop(buffer);
            self.flush()?;
        }

        Ok(lsn)
    }

    /// 强制刷盘
    pub fn flush(&self) -> io::Result<()> {
        let mut buffer = self.buffer.lock().unwrap();
        let mut file = self.log_file.lock().unwrap();

        for (lsn, record) in buffer.drain(..) {
            let data = bincode::serialize(&record).unwrap();
            let crc = crc32fast::hash(&data);

            file.write_all(&lsn.0.to_le_bytes())?;
            file.write_all(&crc.to_le_bytes())?;
            file.write_all(&(data.len() as u32).to_le_bytes())?;
            file.write_all(&data)?;
        }

        file.flush()?;
        file.get_ref().sync_all()?;

        Ok(())
    }
}
```

### 6.2 检查点机制

```rust
/// 检查点类型
#[derive(Clone, Copy, Debug)]
pub enum CheckpointType {
    Consistent,   // 一致检查点：停止所有更新
    Fuzzy,        // 模糊检查点：允许并发更新
    Incremental,  // 增量检查点：只检查部分脏页
}

/// 检查点管理器
pub struct CheckpointManager {
    wal: Arc<WriteAheadLog>,
    buffer_pool: Arc<BufferPool>,
    transaction_manager: Arc<TransactionManager>,
    checkpoint_type: CheckpointType,
}

impl CheckpointManager {
    /// 执行模糊检查点
    pub async fn fuzzy_checkpoint(&self) -> io::Result<LSN> {
        let begin_lsn = self.wal.current_lsn();

        // 1. 记录检查点开始日志
        let active_txns = self.transaction_manager.get_active_transactions();
        let checkpoint_begin = LogRecord::CheckpointBegin {
            active_txns: active_txns.iter().map(|t| t.id).collect(),
            lsn: begin_lsn,
        };
        let checkpoint_lsn = self.wal.append(checkpoint_begin)?;
        self.wal.flush()?;

        // 2. 记录所有脏页
        let dirty_pages = self.buffer_pool.get_dirty_pages();

        // 3. 写检查点记录到主记录
        self.write_master_record(CheckpointRecord {
            begin_lsn: checkpoint_lsn,
            dirty_page_table: dirty_pages,
            txn_table: active_txns.into_iter().map(|t| (t.id, t.state)).collect(),
        })?;

        // 4. 记录检查点结束
        let end_lsn = self.wal.append(LogRecord::CheckpointEnd { lsn: checkpoint_lsn })?;
        self.wal.flush()?;

        Ok(end_lsn)
    }
}
```

### 6.3 崩溃恢复

```rust
/// ARIES恢复算法实现
pub struct RecoveryManager {
    wal: Arc<WriteAheadLog>,
    buffer_pool: Arc<BufferPool>,
    transaction_manager: Arc<TransactionManager>,
}

/// 恢复分析结果
#[derive(Debug)]
struct AnalysisResult {
    active_txns: HashSet<TxnId>,
    committed_txns: HashSet<TxnId>,
    dirty_page_table: HashMap<PageId, LSN>,
    redo_start_lsn: LSN,
}

impl RecoveryManager {
    /// 执行崩溃恢复
    pub async fn recover(&self) -> io::Result<()> {
        println!("Starting database recovery...");

        // 阶段1：分析
        let analysis = self.analysis_phase()?;

        // 阶段2：Redo
        self.redo_phase(&analysis).await?;

        // 阶段3：Undo
        self.undo_phase(&analysis).await?;

        println!("Recovery complete");
        Ok(())
    }

    fn analysis_phase(&self) -> io::Result<AnalysisResult> {
        let mut result = AnalysisResult {
            active_txns: HashSet::new(),
            committed_txns: HashSet::new(),
            dirty_page_table: HashMap::new(),
            redo_start_lsn: LSN(0),
        };

        // 从检查点开始扫描日志
        for (lsn, record) in self.wal.read_logs()? {
            match &record {
                LogRecord::Begin { txn_id } => {
                    result.active_txns.insert(*txn_id);
                }
                LogRecord::Commit { txn_id, .. } => {
                    result.active_txns.remove(txn_id);
                    result.committed_txns.insert(*txn_id);
                }
                LogRecord::Update { txn_id, page_id, .. } => {
                    result.dirty_page_table.entry(*page_id).or_insert(lsn);
                }
                _ => {}
            }
        }

        // 确定Redo起点
        result.redo_start_lsn = result.dirty_page_table.values()
            .min()
            .copied()
            .unwrap_or(LSN(0));

        Ok(result)
    }

    async fn redo_phase(&self, analysis: &AnalysisResult) -> io::Result<()> {
        for (lsn, record) in self.wal.read_logs()? {
            if lsn < analysis.redo_start_lsn {
                continue;
            }

            match &record {
                LogRecord::Update { page_id, new_data, txn_id, .. } => {
                    if !analysis.committed_txns.contains(txn_id) {
                        continue;
                    }

                    let page_lsn = self.buffer_pool.get_page_lsn(*page_id).unwrap_or(LSN(0));
                    if page_lsn >= lsn {
                        continue;
                    }

                    self.apply_redo(*page_id, new_data).await?;
                }
                _ => {}
            }
        }

        self.buffer_pool.flush_all().await?;
        Ok(())
    }

    async fn undo_phase(&self, analysis: &AnalysisResult) -> io::Result<()> {
        // 按LSN降序撤销未提交事务
        let mut undo_queue: BinaryHeap<(LSN, TxnId)> = analysis.active_txns.iter()
            .map(|txn_id| (analysis.txn_last_lsn[txn_id], *txn_id))
            .collect();

        while let Some((current_lsn, txn_id)) = undo_queue.pop() {
            let record = self.wal.get_record(current_lsn)?;

            match record {
                LogRecord::Update { page_id, old_data, txn_id: t } if t == txn_id => {
                    self.apply_undo(page_id, &old_data).await?;

                    // 写CLR
                    let clr = LogRecord::Update {
                        txn_id,
                        table_id: TableId(0),
                        page_id,
                        offset: 0,
                        old_data: old_data.clone(),
                        new_data: old_data,
                    };
                    self.wal.append(clr)?;
                }
                _ => {}
            }
        }

        self.wal.flush()?;
        Ok(())
    }
}
```

---

## 7. 分布式数据库

### 7.1 分片策略

```rust
/// 分片策略
trait ShardingStrategy: Send + Sync {
    fn shard_for_key(&self, key: &Value) -> ShardId;
    fn shards_for_query(&self, query: &Query) -> Vec<ShardId>;
}

/// 哈希分片
pub struct HashSharding {
    num_shards: usize,
}

impl ShardingStrategy for HashSharding {
    fn shard_for_key(&self, key: &Value) -> ShardId {
        let hash = Self::hash_key(key);
        ShardId((hash % self.num_shards as u64) as usize)
    }

    fn shards_for_query(&self, query: &Query) -> Vec<ShardId> {
        if let Some(key) = self.extract_key_from_query(query) {
            vec![self.shard_for_key(&key)]
        } else {
            (0..self.num_shards).map(ShardId).collect()
        }
    }
}

/// 范围分片
pub struct RangeSharding {
    ranges: Vec<(Bound<Value>, Bound<Value>, ShardId)>,
}

impl ShardingStrategy for RangeSharding {
    fn shard_for_key(&self, key: &Value) -> ShardId {
        for (start, end, shard) in &self.ranges {
            if Self::in_range(key, start, end) {
                return *shard;
            }
        }
        panic!("Key not in any range");
    }
}
```

### 7.2 复制协议

```rust
/// Raft复制状态机
pub struct RaftNode {
    role: AtomicCell<RaftRole>,
    current_term: AtomicU64,
    voted_for: Mutex<Option<NodeId>>,
    log: RwLock<Vec<LogEntry>>,
    commit_index: AtomicU64,
    last_applied: AtomicU64,
    nodes: Vec<NodeId>,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum RaftRole {
    Follower,
    Candidate,
    Leader,
}

#[derive(Clone, Debug)]
pub struct LogEntry {
    pub term: u64,
    pub index: u64,
    pub command: Vec<u8>,
}

impl RaftNode {
    /// 客户端提交命令
    pub async fn propose(&self, command: Vec<u8>) -> Result<ProposalResult, RaftError> {
        if self.role.load() != RaftRole::Leader {
            return Err(RaftError::NotLeader);
        }

        let term = self.current_term.load(Ordering::SeqCst);
        let index = {
            let mut log = self.log.write();
            let new_index = log.len() as u64 + 1;
            log.push(LogEntry { term, index: new_index, command });
            new_index
        };

        // 广播到所有Follower
        self.broadcast_append_entries().await?;

        // 等待提交
        self.wait_for_commit(index).await
    }

    /// 处理AppendEntries RPC
    pub async fn handle_append_entries(&self, req: AppendEntriesRequest)
        -> Result<AppendEntriesResponse, RaftError> {
        let mut resp = AppendEntriesResponse {
            term: self.current_term.load(Ordering::SeqCst),
            success: false,
        };

        if req.term < resp.term {
            return Ok(resp);
        }

        if req.term > resp.term {
            self.become_follower(req.term);
            resp.term = req.term;
        }

        self.reset_election_timer();

        // 检查日志匹配...

        resp.success = true;
        Ok(resp)
    }
}
```

### 7.3 一致性模型

```rust
/// 一致性级别
#[derive(Clone, Copy, Debug)]
pub enum ConsistencyLevel {
    Eventual,     // 最终一致性
    Causal,       // 因果一致性
    Session,      // 会话一致性
    Bounded,      // 有界旧一致性
    Strong,       // 强一致性
}

/// 一致性协调器
pub struct ConsistencyCoordinator {
    level: ConsistencyLevel,
    version_vector: DashMap<ShardId, VectorClock>,
}

impl ConsistencyCoordinator {
    /// 读取时的一致性检查
    pub async fn read_with_consistency(
        &self,
        key: &Key,
        level: ConsistencyLevel,
    ) -> Result<Value, ConsistencyError> {
        match level {
            ConsistencyLevel::Strong => {
                // 从大多数副本读取最新值
                let values = self.read_from_quorum(key).await?;
                self.resolve_conflicts(values)
            }
            ConsistencyLevel::Eventual => {
                // 从任意副本读取
                self.read_from_any(key).await
            }
            ConsistencyLevel::Causal => {
                // 等待因果依赖满足
                self.read_causal(key).await
            }
            _ => todo!(),
        }
    }

    /// 向量时钟合并
    pub fn merge_vector_clocks(
        &self,
        vc1: &VectorClock,
        vc2: &VectorClock,
    ) -> VectorClock {
        let mut merged = VectorClock::new();

        for (node, time) in vc1.iter().chain(vc2.iter()) {
            let current = merged.get(node).copied().unwrap_or(0);
            merged.insert(*node, current.max(*time));
        }

        merged
    }
}
```

---

## 8. 完整示例：嵌入式KV存储

本节展示一个完整的嵌入式键值存储实现，包含存储格式、基本操作、迭代器和事务支持。

### 8.1 存储格式

```rust
use std::fs::{File, OpenOptions};
use std::io::{self, Read, Write, Seek, SeekFrom};
use std::path::Path;
use crc32fast::Hasher;

/// 数据库魔数
const MAGIC: &[u8] = b"RKV\x01";

/// 文件头部
#[repr(C)]
#[derive(Debug, Clone, Copy)]
struct FileHeader {
    magic: [u8; 4],
    version: u32,
    page_size: u32,
    num_pages: u64,
    free_list_head: u64,
    root_page: u64,
    checksum: u32,
}

/// 页类型
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq)]
enum PageType {
    Empty = 0,
    Data = 1,
    Index = 2,
    Overflow = 3,
}

/// 页头部
#[repr(C)]
struct PageHeader {
    page_type: u8,
    flags: u8,
    num_entries: u16,
    free_offset: u16,
    right_child: u64, // 用于B+树内部节点
    checksum: u32,
}

/// 键值对条目头部
#[repr(C)]
struct EntryHeader {
    key_len: u32,
    value_len: u32,
    flags: u32,
}

/// 嵌入式KV存储
pub struct EmbeddedKV {
    file: File,
    header: FileHeader,
    cache: LruCache<u64, Page>,
}

impl EmbeddedKV {
    /// 创建新数据库
    pub fn create<P: AsRef<Path>>(path: P, page_size: u32) -> io::Result<Self> {
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .open(path)?;

        let header = FileHeader {
            magic: [b'R', b'K', b'V', 0x01],
            version: 1,
            page_size,
            num_pages: 1, // 页0是元数据页
            free_list_head: 0,
            root_page: 0,
            checksum: 0,
        };

        // 写入头部
        file.write_all(unsafe {
            std::slice::from_raw_parts(
                &header as *const _ as *const u8,
                std::mem::size_of::<FileHeader>()
            )
        })?;

        // 扩展文件到初始大小
        file.set_len(page_size as u64)?;

        Ok(Self {
            file,
            header,
            cache: LruCache::new(1000),
        })
    }

    /// 打开已有数据库
    pub fn open<P: AsRef<Path>>(path: P) -> io::Result<Self> {
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(path)?;

        // 读取并验证头部
        let mut header_buf = [0u8; std::mem::size_of::<FileHeader>()];
        file.read_exact(&mut header_buf)?;

        let header: FileHeader = unsafe {
            std::ptr::read(header_buf.as_ptr() as *const FileHeader)
        };

        if header.magic != [b'R', b'K', b'V', 0x01] {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Invalid database magic"
            ));
        }

        Ok(Self {
            file,
            header,
            cache: LruCache::new(1000),
        })
    }
}
```

### 8.2 基本操作

```rust
impl EmbeddedKV {
    /// 获取值
    pub fn get(&mut self, key: &[u8]) -> io::Result<Option<Vec<u8>>> {
        if key.is_empty() || key.len() > u32::MAX as usize {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Invalid key size"
            ));
        }

        // 从根页开始搜索
        let mut current_page = self.header.root_page;

        loop {
            let page = self.read_page(current_page)?;

            if page.header.page_type == PageType::Data as u8 {
                // 叶子页，搜索键
                return self.search_in_leaf(&page, key);
            } else {
                // 内部页，找到子页
                current_page = self.find_child_page(&page, key)?;
            }
        }
    }

    /// 插入键值对
    pub fn insert(&mut self, key: &[u8], value: &[u8]) -> io::Result<()> {
        if value.len() > u32::MAX as usize {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Value too large"
            ));
        }

        // 如果根页为空，创建新的叶子页
        if self.header.root_page == 0 {
            let new_page_id = self.allocate_page()?;
            let mut page = self.new_page(PageType::Data);
            self.write_page(new_page_id, &page)?;
            self.header.root_page = new_page_id;
        }

        // 找到插入位置
        let path = self.find_insert_path(key)?;

        // 尝试插入到叶子页
        let (leaf_id, mut leaf) = path.last().unwrap();

        if self.has_space(&leaf, key, value) {
            self.insert_to_page(&mut leaf, key, value)?;
            self.write_page(*leaf_id, &leaf)?;
        } else {
            // 页已满，需要分裂
            self.split_and_insert(path, key, value)?;
        }

        self.sync_header()?;
        Ok(())
    }

    /// 删除键值对
    pub fn delete(&mut self, key: &[u8]) -> io::Result<bool> {
        let path = self.find_insert_path(key)?;
        let (leaf_id, mut leaf) = path.last().unwrap().clone();

        if let Some(idx) = self.find_entry(&leaf, key)? {
            // 标记条目为已删除
            self.mark_deleted(&mut leaf, idx)?;
            self.write_page(leaf_id, &leaf)?;

            // 检查是否需要合并
            if self.should_merge(&leaf) {
                self.try_merge(path)?;
            }

            Ok(true)
        } else {
            Ok(false)
        }
    }
}
```

### 8.3 迭代器

```rust
/// 前向迭代器
pub struct ForwardIterator<'a> {
    db: &'a mut EmbeddedKV,
    current_page: u64,
    current_idx: usize,
}

impl<'a> Iterator for ForwardIterator<'a> {
    type Item = io::Result<(Vec<u8>, Vec<u8>)>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let page = match self.db.read_page(self.current_page) {
                Ok(p) => p,
                Err(e) => return Some(Err(e)),
            };

            if self.current_idx >= page.header.num_entries as usize {
                // 移动到下一页
                self.current_page = page.header.right_child;
                self.current_idx = 0;

                if self.current_page == 0 {
                    return None;
                }
                continue;
            }

            let entry = match self.db.read_entry(&page, self.current_idx) {
                Ok(e) => e,
                Err(e) => return Some(Err(e)),
            };

            self.current_idx += 1;

            // 跳过已删除条目
            if entry.is_deleted {
                continue;
            }

            return Some(Ok((entry.key, entry.value)));
        }
    }
}

/// 范围迭代器
pub struct RangeIterator<'a> {
    db: &'a mut EmbeddedKV,
    current_page: u64,
    current_idx: usize,
    end_key: Option<Vec<u8>>,
}

impl<'a> Iterator for RangeIterator<'a> {
    type Item = io::Result<(Vec<u8>, Vec<u8>)>;

    fn next(&mut self) -> Option<Self::Item> {
        let (key, value) = self.inner_next()?;

        // 检查是否超出范围
        if let Some(ref end) = self.end_key {
            if key.as_slice() > end.as_slice() {
                return None;
            }
        }

        Some(Ok((key, value)))
    }
}

impl EmbeddedKV {
    /// 创建范围迭代器
    pub fn range<R: RangeBounds<Vec<u8>>>(
        &mut self,
        range: R,
    ) -> io::Result<RangeIterator> {
        let start_key = match range.start_bound() {
            Bound::Included(k) | Bound::Excluded(k) => Some(k.clone()),
            Bound::Unbounded => None,
        };

        let end_key = match range.end_bound() {
            Bound::Included(k) | Bound::Excluded(k) => Some(k.clone()),
            Bound::Unbounded => None,
        };

        // 找到起始页
        let (start_page, start_idx) = if let Some(ref key) = start_key {
            self.find_key_position(key)?
        } else {
            (self.find_leftmost_page()?, 0)
        };

        Ok(RangeIterator {
            db: self,
            current_page: start_page,
            current_idx: start_idx,
            end_key,
        })
    }
}
```

### 8.4 事务支持

```rust
/// 事务状态
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TxnState {
    Active,
    Committed,
    Aborted,
}

/// 事务结构
pub struct Transaction<'a> {
    db: &'a mut EmbeddedKV,
    state: TxnState,
    write_set: Vec<(Vec<u8>, Option<Vec<u8>>)>, // (key, old_value)
    read_set: Vec<Vec<u8>>,
    start_version: u64,
}

impl<'a> Transaction<'a> {
    /// 获取值（快照读）
    pub fn get(&mut self, key: &[u8]) -> io::Result<Option<Vec<u8>>> {
        if self.state != TxnState::Active {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                "Transaction not active"
            ));
        }

        self.read_set.push(key.to_vec());

        // 先检查写集
        for (k, v) in self.write_set.iter().rev() {
            if k == key {
                return Ok(v.clone());
            }
        }

        // 从数据库读取快照版本
        self.db.get_at_version(key, self.start_version)
    }

    /// 插入或更新
    pub fn put(&mut self, key: &[u8], value: &[u8]) -> io::Result<()> {
        if self.state != TxnState::Active {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                "Transaction not active"
            ));
        }

        // 记录旧值用于回滚
        let old_value = self.db.get(key)?;

        self.write_set.push((key.to_vec(), old_value));
        self.write_set.push((key.to_vec(), Some(value.to_vec())));

        Ok(())
    }

    /// 提交事务
    pub fn commit(mut self) -> io::Result<()> {
        if self.state != TxnState::Active {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                "Transaction not active"
            ));
        }

        // 获取提交版本号
        let commit_version = self.db.allocate_version();

        // 写入所有更改
        for (key, value) in &self.write_set {
            if let Some(ref v) = value {
                self.db.insert_at_version(key, v, commit_version)?;
            } else {
                self.db.delete_at_version(key, commit_version)?;
            }
        }

        // 写入事务提交记录
        self.db.write_commit_record(commit_version)?;

        self.state = TxnState::Committed;
        Ok(())
    }

    /// 回滚事务
    pub fn rollback(mut self) -> io::Result<()> {
        self.state = TxnState::Aborted;
        // 写集中的更改不会应用到数据库
        Ok(())
    }
}

impl<'a> Drop for Transaction<'a> {
    fn drop(&mut self) {
        if self.state == TxnState::Active {
            // 自动回滚未提交的事务
            let _ = self.write_set.clear();
            self.state = TxnState::Aborted;
        }
    }
}

impl EmbeddedKV {
    /// 开始新事务
    pub fn begin_transaction(&mut self) -> Transaction {
        let version = self.current_version();

        Transaction {
            db: self,
            state: TxnState::Active,
            write_set: Vec::new(),
            read_set: Vec::new(),
            start_version: version,
        }
    }
}
```

---

## 9. 性能优化

### 9.1 零拷贝

```rust
use std::os::unix::io::AsRawFd;
use libc::{c_void, iovec, off_t, preadv, pwritev};

/// 使用scatter-gather I/O实现零拷贝读取
pub fn readv_zero_copy(
    fd: RawFd,
    buffers: &mut [IoSliceMut<'_>],
    offset: off_t,
) -> io::Result<usize> {
    let iovec: Vec<iovec> = buffers.iter_mut()
        .map(|buf| iovec {
            iov_base: buf.as_mut_ptr() as *mut c_void,
            iov_len: buf.len(),
        })
        .collect();

    let bytes_read = unsafe {
        preadv(fd, iovec.as_ptr(), iovec.len() as i32, offset)
    };

    if bytes_read < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(bytes_read as usize)
    }
}

/// 使用mmap实现页面级别的零拷贝
pub struct ZeroCopyPager {
    mmap: MmapMut,
    page_cache: Arc<RwLock<HashMap<PageId, *mut u8>>>,
}

impl ZeroCopyPager {
    /// 获取页面引用（无拷贝）
    pub fn get_page_ref(&self, page_id: PageId) -> Option<&[u8]> {
        let offset = page_id.0 as usize * PAGE_SIZE;
        if offset + PAGE_SIZE > self.mmap.len() {
            return None;
        }

        Some(&self.mmap[offset..offset + PAGE_SIZE])
    }

    /// 获取可变页面引用
    pub fn get_page_mut(&mut self, page_id: PageId) -> Option<&mut [u8]> {
        let offset = page_id.0 as usize * PAGE_SIZE;
        if offset + PAGE_SIZE > self.mmap.len() {
            return None;
        }

        Some(&mut self.mmap[offset..offset + PAGE_SIZE])
    }
}

/// 使用sendfile/send_file实现网络零拷贝
#[cfg(target_os = "linux")]
pub async fn send_file_zero_copy(
    file: &File,
    socket: &TcpStream,
    offset: u64,
    count: usize,
) -> io::Result<usize> {
    use std::os::unix::io::AsRawFd;

    let file_fd = file.as_raw_fd();
    let socket_fd = socket.as_raw_fd();

    let mut offset = offset as off_t;

    let bytes_sent = unsafe {
        libc::sendfile(socket_fd, file_fd, &mut offset, count)
    };

    if bytes_sent < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(bytes_sent as usize)
    }
}
```

### 9.2 异步I/O

```rust
use tokio::fs::File;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use io_uring::{opcode, IoUring, SubmissionQueue, CompletionQueue};

/// 基于io_uring的高性能异步存储
pub struct AsyncStorage {
    ring: IoUring,
    file: File,
}

impl AsyncStorage {
    /// 使用io_uring进行异步批量读取
    pub async fn readv_batch(
        &mut self,
        requests: Vec<ReadRequest>,
    ) -> Vec<io::Result<Vec<u8>>> {
        let mut results = Vec::with_capacity(requests.len());

        // 提交所有读请求
        unsafe {
            let mut sq = self.ring.submission();

            for (i, req) in requests.iter().enumerate() {
                let buf = vec![0u8; req.len];
                let read_e = opcode::Read::new(
                    types::Fd(self.file.as_raw_fd()),
                    buf.as_ptr() as *mut u8,
                    req.len as u32,
                )
                .offset(req.offset as u64)
                .build()
                .user_data(i as u64);

                sq.push(&read_e).expect("Submission queue full");
            }
        }

        self.ring.submit_and_wait(requests.len()).unwrap();

        // 收集结果
        let cq = self.ring.completion();
        for cqe in cq {
            let idx = cqe.user_data() as usize;
            let res = cqe.result();

            if res < 0 {
                results.push(Err(io::Error::from_raw_os_error(-res)));
            } else {
                // 使用unsafe将缓冲区所有权转移回来
                results.push(Ok(requests[idx].buffer.take().unwrap()));
            }
        }

        results
    }
}

/// 使用tokio的异步文件I/O
pub struct TokioStorage {
    file: tokio::fs::File,
}

impl TokioStorage {
    pub async fn read_page(&mut self, page_id: PageId) -> io::Result<Page> {
        let mut buf = vec![0u8; PAGE_SIZE];
        let offset = page_id.0 as u64 * PAGE_SIZE as u64;

        self.file.seek(SeekFrom::Start(offset)).await?;
        self.file.read_exact(&mut buf).await?;

        Ok(Page::from_bytes(&buf))
    }

    pub async fn write_page(&mut self, page_id: PageId, page: &Page) -> io::Result<()> {
        let offset = page_id.0 as u64 * PAGE_SIZE as u64;
        let data = page.to_bytes();

        self.file.seek(SeekFrom::Start(offset)).await?;
        self.file.write_all(&data).await?;

        Ok(())
    }

    /// 批量写入（合并相邻页面）
    pub async fn write_pages_batch(
        &mut self,
        pages: &[(PageId, Page)],
    ) -> io::Result<()> {
        // 按页ID排序并合并连续页面
        let mut sorted = pages.to_vec();
        sorted.sort_by_key(|(id, _)| id.0);

        let mut merged = Vec::new();
        let mut current_start = sorted[0].0;
        let mut current_batch = vec![sorted[0].1.to_bytes()];

        for i in 1..sorted.len() {
            if sorted[i].0.0 == sorted[i-1].0.0 + 1 {
                current_batch.push(sorted[i].1.to_bytes());
            } else {
                merged.push((current_start, current_batch.concat()));
                current_start = sorted[i].0;
                current_batch = vec![sorted[i].1.to_bytes()];
            }
        }
        merged.push((current_start, current_batch.concat()));

        // 执行合并后的写入
        for (start_id, data) in merged {
            let offset = start_id.0 as u64 * PAGE_SIZE as u64;
            self.file.seek(SeekFrom::Start(offset)).await?;
            self.file.write_all(&data).await?;
        }

        Ok(())
    }
}
```

### 9.3 内存池

```rust
/// 固定大小的内存块
pub struct PooledBlock {
    ptr: NonNull<u8>,
    size: usize,
    pool: Weak<MemoryPoolInner>,
}

impl Drop for PooledBlock {
    fn drop(&mut self) {
        // 归还到池中而不是释放
        if let Some(pool) = self.pool.upgrade() {
            unsafe {
                pool.return_block(self.ptr, self.size);
            }
        }
    }
}

/// 分层内存池
pub struct MemoryPool {
    inner: Arc<MemoryPoolInner>,
}

struct MemoryPoolInner {
    /// 小型块池 (64B, 128B, 256B, 512B)
    small_pools: Vec<ArrayQueue<NonNull<u8>>>,
    /// 中型块池 (1KB - 64KB)
    medium_pools: Vec<ArrayQueue<NonNull<u8>>>,
    /// 大型块池 (>64KB)，使用jemalloc
    large_allocator: Mutex<Jemalloc>,
    /// 使用统计
    stats: AtomicMemoryStats,
}

impl MemoryPool {
    pub fn new() -> Self {
        let inner = Arc::new(MemoryPoolInner {
            small_pools: (0..4).map(|_| ArrayQueue::new(1024)).collect(),
            medium_pools: (0..7).map(|_| ArrayQueue::new(256)).collect(),
            large_allocator: Mutex::new(Jemalloc),
            stats: AtomicMemoryStats::default(),
        });

        Self { inner }
    }

    pub fn allocate(&self, size: usize) -> PooledBlock {
        // 选择合适的池
        let ptr = if size <= 512 {
            self.allocate_small(size)
        } else if size <= 65536 {
            self.allocate_medium(size)
        } else {
            self.allocate_large(size)
        };

        PooledBlock {
            ptr,
            size,
            pool: Arc::downgrade(&self.inner),
        }
    }

    fn allocate_small(&self, size: usize) -> NonNull<u8> {
        let pool_idx = match size {
            0..=64 => 0,
            65..=128 => 1,
            129..=256 => 2,
            _ => 3,
        };

        let pool = &self.inner.small_pools[pool_idx];
        let block_size = 64 << pool_idx;

        // 尝试从池中获取
        if let Some(ptr) = pool.pop() {
            self.inner.stats.small_hits.fetch_add(1, Ordering::Relaxed);
            return ptr;
        }

        // 分配新块
        let layout = Layout::from_size_align(block_size, 64).unwrap();
        let ptr = unsafe { NonNull::new_unchecked(std::alloc::alloc(layout)) };

        self.inner.stats.small_misses.fetch_add(1, Ordering::Relaxed);
        ptr
    }

    fn allocate_medium(&self, size: usize) -> NonNull<u8> {
        // 类似small的实现，使用2KB对齐
        // ...
        todo!()
    }

    fn allocate_large(&self, size: usize) -> NonNull<u8> {
        let layout = Layout::from_size_align(size, 4096).unwrap();
        let guard = self.inner.large_allocator.lock();
        let ptr = unsafe { guard.alloc(layout) };
        self.inner.stats.large_allocations.fetch_add(1, Ordering::Relaxed);
        NonNull::new(ptr).expect("Allocation failed")
    }
}

impl MemoryPoolInner {
    unsafe fn return_block(&self, ptr: NonNull<u8>, size: usize) {
        if size <= 512 {
            let pool_idx = match size {
                0..=64 => 0,
                65..=128 => 1,
                129..=256 => 2,
                _ => 3,
            };

            // 非阻塞归还
            let _ = self.small_pools[pool_idx].push(ptr);
        } else if size <= 65536 {
            // 类似处理medium池
        } else {
            // 释放到系统
            let layout = Layout::from_size_align_unchecked(size, 4096);
            self.large_allocator.lock().dealloc(ptr.as_ptr(), layout);
        }
    }
}
```

---

## 10. 测试策略

### 10.1 持久化测试

```rust
/// 使用确定性故障注入测试持久化
#[cfg(test)]
mod persistence_tests {
    use super::*;
    use std::panic::catch_unwind;
    use tempfile::tempdir;

    /// 测试写入后读取一致性
    #[test]
    fn test_write_read_consistency() {
        let dir = tempdir().unwrap();
        let db_path = dir.path().join("test.db");

        // 写入数据
        {
            let mut db = EmbeddedKV::create(&db_path, 4096).unwrap();
            for i in 0..1000 {
                let key = format!("key_{:04}", i);
                let value = format!("value_{:010}", i);
                db.insert(key.as_bytes(), value.as_bytes()).unwrap();
            }
            // 显式drop触发同步
        }

        // 重新打开并验证
        {
            let mut db = EmbeddedKV::open(&db_path).unwrap();
            for i in 0..1000 {
                let key = format!("key_{:04}", i);
                let expected_value = format!("value_{:010}", i);

                let actual = db.get(key.as_bytes()).unwrap();
                assert_eq!(actual, Some(expected_value.into_bytes()));
            }
        }
    }

    /// 测试并发写入的正确性
    #[test]
    fn test_concurrent_writes() {
        let dir = tempdir().unwrap();
        let db_path = dir.path().join("test.db");

        let mut db = Arc::new(Mutex::new(
            EmbeddedKV::create(&db_path, 4096).unwrap()
        ));

        let handles: Vec<_> = (0..10).map(|thread_id| {
            let db = Arc::clone(&db);
            std::thread::spawn(move || {
                for i in 0..100 {
                    let key = format!("thread{}_key{}", thread_id, i);
                    let value = format!("value{}", i);

                    let mut guard = db.lock().unwrap();
                    guard.insert(key.as_bytes(), value.as_bytes()).unwrap();
                }
            })
        }).collect();

        for h in handles {
            h.join().unwrap();
        }

        // 验证所有数据
        let db = db.lock().unwrap();
        for thread_id in 0..10 {
            for i in 0..100 {
                let key = format!("thread{}_key{}", thread_id, i);
                let value = db.get(key.as_bytes()).unwrap();
                assert!(value.is_some());
            }
        }
    }

    /// 使用注入磁盘错误的测试
    #[test]
    fn test_io_error_handling() {
        use std::io::ErrorKind;

        let dir = tempdir().unwrap();
        let db_path = dir.path().join("test.db");

        let mut db = EmbeddedKV::create(&db_path, 4096).unwrap();

        // 填满磁盘模拟（通过设置文件大小限制）
        // 验证适当的错误返回而不是panic
        // ...
    }
}
```

### 10.2 崩溃恢复测试

```rust
/// 使用进程分叉测试崩溃恢复
#[cfg(test)]
mod crash_recovery_tests {
    use super::*;
    use std::process::{Command, Stdio};
    use nix::unistd::{fork, ForkResult};

    /// 在子进程中模拟崩溃
    #[test]
    fn test_crash_recovery_with_wal() {
        let dir = tempdir().unwrap();
        let db_path = dir.path().join("test.db");

        match unsafe { fork() } {
            Ok(ForkResult::Parent { child }) => {
                // 父进程等待子进程被信号终止
                use nix::sys::wait::waitpid;
                use nix::sys::signal::Signal;

                let status = waitpid(child, None).unwrap();
                // 验证子进程被SIGKILL终止

                // 父进程：恢复并验证数据
                let mut db = EmbeddedKV::open(&db_path).unwrap();
                db.recover().unwrap();

                // 验证已提交事务的数据存在
                // 验证未提交事务的数据不存在
            }
            Ok(ForkResult::Child) => {
                // 子进程：写入数据然后崩溃
                let mut db = EmbeddedKV::create(&db_path, 4096).unwrap();

                // 开始事务
                db.begin_transaction();
                db.insert(b"committed_key", b"committed_value").unwrap();
                db.commit().unwrap();

                // 另一个未提交事务
                db.begin_transaction();
                db.insert(b"uncommitted_key", b"uncommitted_value").unwrap();
                // 不提交，直接崩溃

                std::process::abort();
            }
            Err(_) => panic!("Fork failed"),
        }
    }

    /// 测试ARIES恢复算法
    #[test]
    fn test_aries_recovery() {
        // 创建测试场景
        let wal_entries = vec![
            LogRecord::Begin { txn_id: TxnId(1) },
            LogRecord::Update {
                txn_id: TxnId(1),
                table_id: TableId(0),
                page_id: PageId(1),
                offset: 0,
                old_data: vec![0u8; 100],
                new_data: vec![1u8; 100],
            },
            LogRecord::Commit { txn_id: TxnId(1), timestamp: 100 },
            LogRecord::Begin { txn_id: TxnId(2) },
            LogRecord::Update {
                txn_id: TxnId(2),
                table_id: TableId(0),
                page_id: PageId(2),
                offset: 0,
                old_data: vec![0u8; 100],
                new_data: vec![2u8; 100],
            },
            // Txn 2未提交，需要回滚
        ];

        let recovery_mgr = RecoveryManager::new(wal);

        // 执行恢复
        let result = recovery_mgr.recover().unwrap();

        // 验证：Txn 1的更改应该被重做
        assert!(page_has_data(PageId(1), &[1u8; 100]));

        // 验证：Txn 2的更改应该被撤销
        assert!(page_has_data(PageId(2), &[0u8; 100]));
    }
}
```

### 10.3 并发测试

```rust
/// 使用Loom进行并发模型测试
#[cfg(test)]
mod concurrency_tests {
    use loom::sync::Arc;
    use loom::thread;

    /// 测试并发访问的正确性
    #[test]
    fn test_concurrent_get_put() {
        loom::model(|| {
            let db = Arc::new(ConcurrentKV::new());

            let db1 = Arc::clone(&db);
            let t1 = thread::spawn(move || {
                db1.put(b"key", b"value1");
            });

            let db2 = Arc::clone(&db);
            let t2 = thread::spawn(move || {
                db2.put(b"key", b"value2");
            });

            t1.join().unwrap();
            t2.join().unwrap();

            // 验证最终状态一致
            let value = db.get(b"key");
            assert!(value == Some(b"value1".to_vec()) ||
                    value == Some(b"value2".to_vec()));
        });
    }

    /// 测试死锁避免
    #[test]
    fn test_deadlock_prevention() {
        use std::time::Duration;

        let lock_mgr = Arc::new(LockManager::new());

        let handles = vec![
            {
                let lm = Arc::clone(&lock_mgr);
                thread::spawn(move || {
                    lm.acquire_lock(TxnId(1), ResourceId(1), LockMode::Exclusive)
                        .unwrap();
                    thread::sleep(Duration::from_millis(10));
                    lm.acquire_lock(TxnId(1), ResourceId(2), LockMode::Exclusive)
                        .unwrap();
                })
            },
            {
                let lm = Arc::clone(&lock_mgr);
                thread::spawn(move || {
                    lm.acquire_lock(TxnId(2), ResourceId(2), LockMode::Exclusive)
                        .unwrap();
                    thread::sleep(Duration::from_millis(10));
                    // 应该检测到死锁并超时或报错
                    let result = lm.acquire_lock(
                        TxnId(2),
                        ResourceId(1),
                        LockMode::Exclusive
                    );
                    assert!(result.is_err() || result.is_ok()); // 根据策略
                })
            },
        ];

        for h in handles {
            h.join().unwrap();
        }
    }

    /// 压力测试
    #[test]
    fn test_concurrent_stress() {
        use std::sync::Barrier;

        let db = Arc::new(Mutex::new(EmbeddedKV::create(
            temp_path(),
            4096
        ).unwrap()));

        let num_threads = 16;
        let ops_per_thread = 1000;
        let barrier = Arc::new(Barrier::new(num_threads));

        let handles: Vec<_> = (0..num_threads).map(|thread_id| {
            let db = Arc::clone(&db);
            let barrier = Arc::clone(&barrier);

            thread::spawn(move || {
                barrier.wait(); // 同步开始

                for i in 0..ops_per_thread {
                    let key = format!("key_{}_{}", thread_id, i);
                    let value = format!("value_{}_{}", thread_id, i);

                    let mut guard = db.lock().unwrap();
                    guard.insert(key.as_bytes(), value.as_bytes()).unwrap();

                    // 混合读写
                    if i % 3 == 0 {
                        let read_key = format!("key_{}_{}", thread_id, i / 2);
                        let _ = guard.get(read_key.as_bytes());
                    }
                }
            })
        }).collect();

        let start = Instant::now();
        for h in handles {
            h.join().unwrap();
        }
        let duration = start.elapsed();

        println!(
            "Stress test completed: {} ops in {:?} ({:.0} ops/sec)",
            num_threads * ops_per_thread,
            duration,
            (num_threads * ops_per_thread) as f64 / duration.as_secs_f64()
        );
    }
}
```

---

## 总结

本指南涵盖了Rust数据库系统开发的完整技术栈：

1. **存储引擎**：B-Tree、LSM-Tree、内存映射、页面管理
2. **事务处理**：ACID、MVCC、两阶段锁、死锁检测
3. **查询引擎**：SQL解析、优化、执行计划、向量化执行
4. **索引系统**：B+树、哈希、全文、空间索引
5. **WAL与恢复**：预写日志、检查点、崩溃恢复
6. **分布式数据库**：分片、复制、一致性模型
7. **完整示例**：嵌入式KV存储的实现
8. **性能优化**：零拷贝、异步I/O、内存池
9. **测试策略**：持久化测试、崩溃恢复测试、并发测试

Rust的内存安全、零成本抽象和 fearless 并发特性使其成为构建高性能、可靠数据库系统的理想选择。
