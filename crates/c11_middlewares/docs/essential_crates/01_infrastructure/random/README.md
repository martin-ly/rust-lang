# 随机数生成

> **核心库**: rand, uuid, getrandom  
> **适用场景**: 随机数、UUID、密码学安全随机、测试数据

---

## 📋 核心库

### rand - 通用随机数生成

**特点**:

- ✅ 功能全面、生态丰富
- ✅ 支持多种 RNG 算法
- ✅ 密码学安全选项 (OsRng)
- ✅ 分布采样支持

**快速示例**:

```rust
use rand::{Rng, thread_rng};
use rand::distributions::{Alphanumeric, Uniform};

fn main() {
    let mut rng = thread_rng();
    
    // 生成随机数
    let n: u32 = rng.gen();
    println!("Random u32: {}", n);
    
    // 范围随机数
    let dice = rng.gen_range(1..=6);
    println!("Dice: {}", dice);
    
    // 随机字符串
    let token: String = (0..32)
        .map(|_| rng.sample(Alphanumeric) as char)
        .collect();
    println!("Token: {}", token);
    
    // 从数组中随机选择
    let choices = ["apple", "banana", "cherry"];
    let choice = choices[rng.gen_range(0..choices.len())];
    println!("Choice: {}", choice);
}
```

**密码学安全**:

```rust
use rand::rngs::OsRng;
use rand::RngCore;

fn generate_secure_key() -> [u8; 32] {
    let mut key = [0u8; 32];
    OsRng.fill_bytes(&mut key);
    key
}

fn main() {
    let key = generate_secure_key();
    println!("Secure key: {:?}", key);
}
```

---

### uuid - UUID 生成

**特点**:

- ✅ 符合 RFC 4122 标准
- ✅ 支持 v1, v3, v4, v5, v6, v7
- ✅ 高性能、零分配

**快速示例**:

```rust
use uuid::Uuid;

fn main() {
    // UUID v4 (随机)
    let id = Uuid::new_v4();
    println!("UUID v4: {}", id);
    
    // 转换格式
    println!("Hyphenated: {}", id.hyphenated());
    println!("Simple: {}", id.simple());
    println!("URN: {}", id.urn());
    
    // 解析 UUID
    let parsed = Uuid::parse_str("550e8400-e29b-41d4-a716-446655440000").unwrap();
    println!("Parsed: {}", parsed);
}
```

---

### getrandom - 系统随机源

**特点**:

- ✅ 直接访问操作系统的 CSPRNG
- ✅ 零依赖、最小化
- ✅ 跨平台支持

```rust
use getrandom::getrandom;

fn main() {
    let mut buf = [0u8; 16];
    getrandom(&mut buf).unwrap();
    println!("Random bytes: {:?}", buf);
}
```

---

## 💡 最佳实践

### 1. 选择正确的 RNG

```rust
use rand::{thread_rng, rngs::OsRng};

// ✅ 一般用途 - 快速但非密码学安全
let mut rng = thread_rng();
let n = rng.gen::<u32>();

// ✅ 密码学用途 - 安全但较慢
let secure_n = OsRng.next_u32();
```

### 2. 生成测试数据

```rust
use rand::{Rng, thread_rng};
use rand::distributions::Alphanumeric;

fn generate_test_user() -> User {
    let mut rng = thread_rng();
    User {
        id: rng.gen(),
        name: (0..10).map(|_| rng.sample(Alphanumeric) as char).collect(),
        age: rng.gen_range(18..80),
    }
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
