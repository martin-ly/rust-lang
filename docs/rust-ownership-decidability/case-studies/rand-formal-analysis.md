# Rand 随机数生成形式化分析

> **主题**: 密码学安全的随机数生成
>
> **形式化框架**: 伪随机性 + 统计测试
>
> **参考**: Rand Documentation; Cryptographic RNG

---

## 目录

- [Rand 随机数生成形式化分析](#rand-随机数生成形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. RNG trait层次](#2-rng-trait层次)
    - [2.1 RngCore基础](#21-rngcore基础)
    - [定义 2.1 (RngCore)](#定义-21-rngcore)
    - [定理 2.1 (RngCore最小接口)](#定理-21-rngcore最小接口)
    - [2.2 Rng扩展](#22-rng扩展)
    - [定义 2.2 (Rng trait)](#定义-22-rng-trait)
    - [定理 2.2 (类型安全生成)](#定理-22-类型安全生成)
  - [3. 随机数生成器](#3-随机数生成器)
    - [3.1 算法实现](#31-算法实现)
    - [3.2 密码学安全](#32-密码学安全)
    - [定理 3.1 (CryptoRng标记)](#定理-31-cryptorng标记)
  - [4. 分布采样](#4-分布采样)
    - [4.1 均匀分布](#41-均匀分布)
    - [定理 4.1 (gen\_range均匀性)](#定理-41-gen_range均匀性)
    - [4.2 加权选择](#42-加权选择)
    - [定理 4.2 (加权分布正确性)](#定理-42-加权分布正确性)
  - [5. 种子与可重现性](#5-种子与可重现性)
    - [定理 5.1 (SeedableRng)](#定理-51-seedablerng)
  - [6. 线程安全](#6-线程安全)
    - [定理 6.1 (ThreadRng)](#定理-61-threadrng)
    - [定理 6.2 (`Arc<Mutex<Rng>>`)](#定理-62-arcmutexrng)
  - [7. 反例与安全性](#7-反例与安全性)
    - [反例 7.1 (不可重现测试)](#反例-71-不可重现测试)
    - [反例 7.2 (不安全密钥生成)](#反例-72-不安全密钥生成)
    - [反例 7.3 (模偏差)](#反例-73-模偏差)
  - [参考文献](#参考文献)

---

## 1. 引言

Rand crate提供:

- **多种RNG算法**: ChaCha20, StdRng, SmallRng等
- **分布采样**: 均匀、正态、加权等
- **密码学安全**: CryptoRng trait标记
- **可重现性**: 种子控制

---

## 2. RNG trait层次

### 2.1 RngCore基础

### 定义 2.1 (RngCore)

```rust
pub trait RngCore {
    fn next_u32(&mut self) -> u32;
    fn next_u64(&mut self) -> u64;
    fn fill_bytes(&mut self, dest: &mut [u8]);
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error>;
}
```

### 定理 2.1 (RngCore最小接口)

> 只需实现next_u32，其他有默认实现。

**证明**:

```rust
impl RngCore for MyRng {
    fn next_u32(&mut self) -> u32 {
        // 必须实现
        self.state = self.state.wrapping_mul(747796405).wrapping_add(2891336453);
        self.state
    }
}

// next_u64, fill_bytes 有基于next_u32的默认实现
```

∎

### 2.2 Rng扩展

### 定义 2.2 (Rng trait)

```rust
pub trait Rng: RngCore {
    fn gen<T>(&mut self) -> T where Standard: Distribution<T>;
    fn gen_range<T, R>(&mut self, range: R) -> T;
    fn shuffle<T>(&mut self, slice: &mut [T]);
}
```

### 定理 2.2 (类型安全生成)

> `gen<T>()` 根据类型生成随机值。

**实现**:

```rust
let i: i32 = rng.gen();      // 随机i32
let f: f64 = rng.gen();      // 随机f64 (0..1)
let b: bool = rng.gen();     // 随机bool
```

**类型驱动**: 编译时确定生成逻辑。

∎

---

## 3. 随机数生成器

### 3.1 算法实现

| 生成器 | 速度 | 质量 | 用途 |
|--------|------|------|------|
| StdRng | 中 | 高 | 通用 |
| ChaCha12 | 慢 | 密码学 | 安全随机 |
| SmallRng | 快 | 中 | 模拟/游戏 |
| OsRng | 系统 | 最高 | 密钥生成 |

### 3.2 密码学安全

### 定理 3.1 (CryptoRng标记)

> CryptoRng标记表示算法通过密码学审查。

**定义**:

```rust
pub trait CryptoRng: RngCore {}

impl CryptoRng for ChaCha20Rng {}
impl CryptoRng for OsRng {}
// 不实现 for SmallRng (不够安全)
```

**保证**:

- 不可预测
- 抗统计分析
- 适合密钥生成

∎

---

## 4. 分布采样

### 4.1 均匀分布

### 定理 4.1 (gen_range均匀性)

> gen_range在范围内均匀分布。

**实现**:

```rust
fn gen_range<T, R>(&mut self, range: R) -> T
where
    T: SampleUniform,
    R: SampleRange<T>,
{
    T::Sampler::sample_single(range, self)
}
```

**无偏算法**: 拒绝采样避免模偏差。

∎

### 4.2 加权选择

### 定理 4.2 (加权分布正确性)

> WeightedIndex按权重概率选择。

**证明**:

```rust
use rand::distributions::{Distribution, WeightedIndex};

let choices = ['a', 'b', 'c'];
let weights = [2, 1, 1];  // a: 50%, b: 25%, c: 25%

let dist = WeightedIndex::new(&weights).unwrap();
let choice = choices[dist.sample(&mut rng)];
```

**算法**: 累积分布函数(CDF) + 二分查找。

∎

---

## 5. 种子与可重现性

### 定理 5.1 (SeedableRng)

> 相同种子产生相同序列。

**实现**:

```rust
use rand::SeedableRng;
use rand::rngs::StdRng;

let mut rng1 = StdRng::seed_from_u64(42);
let mut rng2 = StdRng::seed_from_u64(42);

assert_eq!(rng1.gen::<u32>(), rng2.gen::<u32>());  // 相同
```

**用途**:

- 测试可重现
- 模拟回放
- 调试

∎

---

## 6. 线程安全

### 定理 6.1 (ThreadRng)

> ThreadRng是线程局部，无需Sync。

**实现**:

```rust
thread_local! {
    static THREAD_RNG: RefCell<ReseedingRng<ChaCha20Core, OsRng>> = ...;
}
```

**行为**:

- 每线程独立实例
- 无需锁
- 自动播种

∎

### 定理 6.2 (`Arc<Mutex<Rng>>`)

> 共享RNG需要同步。

**模式**:

```rust
use std::sync::{Arc, Mutex};

let rng = Arc::new(Mutex::new(StdRng::from_entropy()));

// 多线程共享
let rng_clone = Arc::clone(&rng);
thread::spawn(move || {
    let n = rng_clone.lock().unwrap().gen::<u32>();
});
```

∎

---

## 7. 反例与安全性

### 反例 7.1 (不可重现测试)

```rust
// 测试可能随机失败
#[test]
fn bad_test() {
    let n = rand::random::<u32>();
    assert!(n > 100);  // 可能失败!
}

// 正确: 固定种子
#[test]
fn good_test() {
    let mut rng = StdRng::seed_from_u64(12345);
    let n = rng.gen::<u32>();
    assert!(n > 100);
}
```

### 反例 7.2 (不安全密钥生成)

```rust
// 不安全: 使用非加密RNG生成密钥
let key: [u8; 32] = SmallRng::from_entropy().gen();

// 正确
let key: [u8; 32] = OsRng.gen();
```

### 反例 7.3 (模偏差)

```rust
// 有偏: 简单取模
let n = rng.gen::<u32>() % 100;  // 不均匀!

// 正确: 使用gen_range
let n = rng.gen_range(0..100);  // 均匀
```

---

## 参考文献

1. **Rand Contributors.** (2024). *Rand Documentation*. <https://docs.rs/rand/>

2. **NIST.** (2015). *Recommendation for Random Number Generation Using Deterministic Random Bit Generators*. SP 800-90A.

---

*文档版本: 1.0.0*
*形式化深度: 高*
*定理数量: 8个*
*最后更新: 2026-03-04*
