# 学习路径指南

> **报告日期**: 2025-10-24
> **最后更新**: 2026-04-10

---

## 🗺️ 推荐学习路径

### 路径 1: 初学者 (4-6 周)

```
C01 (所有权) → C02 (类型) → C03 (控制流)
     ↓              ↓              ↓
  练习          练习          练习
```

### 路径 2: 进阶开发者 (6-8 周)

```
C04 (泛型) → C05 (并发) → C06 (异步)
     ↓           ↓           ↓
  项目实战    项目实战    项目实战
```

### 路径 3: 系统程序员 (8-12 周)

```
C07 (进程) → C08 (算法) → C10 (网络) → C12 (WASM)
     ↓           ↓            ↓            ↓
   系统工具    数据结构     网络服务     Web 应用
```

### 路径 4: Rust 1.96 新特性专题 (2-3 周)

```
第1周: 核心新特性
├── isqrt - 整数平方根运算
├── async Fn trait 改进
└── never_type (!) 基础应用

第2周: 标准库增强
├── HashMap 新 API
├── 字符串处理优化
└── 迭代器改进

第3周: 高级应用
├── spawn_unchecked 线程模式
├── ControlFlow 进阶
└── LazyLock 生产模式
```

---

## 🆕 Rust 1.96 新特性学习路径

### 阶段 1: 快速上手 (第 1-2 天)

| 特性 | 难度 | 学习资源 | 实践目标 |
|------|------|----------|----------|
| `isqrt` | ⭐ 简单 | 标准库文档 | 实现数字处理工具 |
| `HashMap::get_disjoint_mut` | ⭐⭐ 中等 | API 指南 | 优化并发数据结构 |
| `async Fn` 改进 | ⭐⭐⭐ 进阶 | 异步编程指南 | 重构异步代码 |

### 阶段 2: 深度理解 (第 3-5 天)

```rust
// 1. 整数平方根 - 数学计算优化
fn demonstrate_isqrt() {
    let n: u64 = 1000000;
    let sqrt = n.isqrt();  // Rust 1.96: 精确整数平方根
    assert_eq!(sqrt, 1000);

    // 应用于质数检测
    fn is_prime(n: u64) -> bool {
        if n < 2 { return false; }
        for i in 2..=n.isqrt() {
            if n % i == 0 { return false; }
        }
        true
    }
}

// 2. HashMap 并行可变访问
use std::collections::HashMap;

fn parallel_map_access() {
    let mut map = HashMap::new();
    map.insert("a", 1);
    map.insert("b", 2);

    // Rust 1.96: 同时获取多个互斥可变引用
    let [ Some(a), Some(b) ] = map.get_disjoint_mut(["a", "b"]) else {
        panic!("keys not found");
    };
    *a += 10;
    *b += 20;
}

// 3. async Fn trait 使用
async fn use_async_fn_trait() {
    // 更清晰的异步 trait 定义
    async fn process<F>(f: F)
    where
        F: async Fn(i32) -> i32,
    {
        let result = f(42).await;
        println!("{}", result);
    }
}
```

### 阶段 3: 综合应用 (第 6-7 天)

结合 Rust 1.94+ 特性构建完整应用：

```
项目: 高性能数据处理管道
├── 使用 array_windows (1.94) 进行数据窗口分析
├── 使用 isqrt (1.96) 进行几何计算
├── 使用 HashMap 新 API (1.96) 管理状态
└── 使用 async Fn (1.96) 处理异步 I/O
```

---

## 📋 推荐学习顺序

### 对于初学者

```
1. C01 (所有权基础) ──┐
2. C02 (类型系统) ────┼→ Rust 1.96 基础特性
3. C03 (控制流) ──────┘    (isqrt, 基础 API)
      ↓
4. 实践项目: 计算器工具
      ↓
5. 进阶: async/await + 1.96 async Fn 改进
```

### 对于有经验的开发者

```
1. 快速复习 C04 (泛型) + C05 (并发)
      ↓
2. Rust 1.94 特性 (array_windows, ControlFlow, LazyLock)
      ↓
3. Rust 1.96 特性 (isqrt, get_disjoint_mut, async Fn)
      ↓
4. 综合项目: 高性能服务器
```

### 对于系统程序员

```
1. C07 (进程管理) ──┐
2. C08 (算法) ──────┼→ 1.96 系统编程特性
3. C10 (网络) ──────┘    (spawn_unchecked, 底层优化)
      ↓
4. 深入: never_type (!) 在错误处理中的应用
      ↓
5. 项目: 系统监控工具
```

---

## 🛠️ 实践项目建议

### 项目 1: 数学工具库 (初级)

**目标**: 掌握 Rust 1.96 数学相关新特性

**功能清单**:

- [ ] 质数检测器 (使用 `isqrt` 优化)
- [ ] 几何计算器 (距离、面积计算)
- [ ] 统计工具 (均值、标准差)

**涉及特性**:

- `isqrt` - 整数平方根
- `array_windows` (1.94) - 滑动窗口统计

**预计时间**: 2-3 天

### 项目 2: 并发哈希表缓存 (中级)

**目标**: 掌握 1.96 并发数据结构的改进

**功能清单**:

- [ ] 实现 LRU 缓存
- [ ] 使用 `get_disjoint_mut` 并行更新
- [ ] 使用 `LazyLock` 延迟初始化
- [ ] 性能基准测试

**涉及特性**:

- `HashMap::get_disjoint_mut`
- `LazyLock::get` 热路径优化 (1.94+)
- `ControlFlow` 错误处理 (1.94+)

**预计时间**: 4-5 天

### 项目 3: 异步 Web 服务 (高级)

**目标**: 掌握 1.96 异步编程改进

**功能清单**:

- [ ] REST API 服务端
- [ ] 使用 `async Fn` trait 抽象处理器
- [ ] 连接池管理 (使用 1.96 新 API)
- [ ] 错误处理管道 (使用 `ControlFlow`)

**涉及特性**:

- `async Fn` trait 改进
- `ControlFlow` 提前终止
- `LazyLock` 全局配置

**预计时间**: 1-2 周

### 项目 4: 系统监控工具 (专家)

**目标**: 综合应用 1.94-1.96 特性

**功能清单**:

- [ ] 系统资源监控 (CPU、内存)
- [ ] 使用 `spawn_unchecked` (如适用)
- [ ] 高效数据处理管道
- [ ] 配置热重载

**涉及特性**:

- `spawn_unchecked` - 高级线程控制
- `isqrt` - 资源计算
- `never_type` - 错误处理

**预计时间**: 2-3 周

---

## 📚 关键资源

- [QUICK_REFERENCE](./research_notes/QUICK_REFERENCE.md)
- [crates/c01_ownership_borrow_scope](../crates/c01_ownership_borrow_scope/README.md)

---

**状态**: ✅ 已更新
