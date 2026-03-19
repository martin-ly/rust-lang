# 形式化验证实战指南

## 概述

形式化验证使用数学方法证明程序正确性。本指南介绍Rust安全关键系统中形式化验证的实用方法。

---

## 验证工具链

### 工具对比矩阵

| 工具 | 类型 | 自动化 | 适用场景 | 学习曲线 | 性能 |
|------|------|--------|----------|----------|------|
| **Miri** | 解释器/UB检测 | 全自动 | unsafe代码验证 | 低 | 慢 |
| **Kani** | 模型检查 | 全自动 | 属性验证 | 中 | 中等 |
| **Verus** | 定理证明 | 半自动 | 功能正确性 | 高 | 快* |
| **Creusot** | 定理证明 | 半自动 | 复杂不变量 | 高 | 快* |
| **Prusti** | 契约检查 | 自动 | 前置/后置条件 | 中 | 中等 |

*注：证明一旦完成，运行时无开销

### 工具选择决策树

```
需要验证什么？
    │
    ├── 无未定义行为 ──► Miri
    │
    ├── 安全性属性 ──► Kani
    │       │
    │       ├── 数组边界 ──► kani::verify_bound()
    │       │
    │       ├── 无溢出 ──► kani::verify_no_overflow()
    │       │
    │       └── 功能属性 ──► #[kani::proof]
    │
    ├── 功能正确性 ──► Verus/Creusot
    │       │
    │       ├── 复杂算法 ──► Verus
    │       │
    │       └── 数据结构 ──► Creusot
    │
    └── 运行时契约 ──► Prusti
```

---

## Miri实战

### 基础用法

```bash
# 安装
rustup component add miri

# 运行测试
cargo miri test

# 运行特定测试
cargo miri test test_name

# 检查二进制
cargo miri run
```

### 环境变量配置

```bash
# 严格模式
export MIRIFLAGS="-Zmiri-strict-provenance -Zmiri-symbolic-alignment-check"

# 忽略隔离（允许文件系统操作）
export MIRIFLAGS="-Zmiri-disable-isolation"

# 检查数据竞争
export MIRIFLAGS="-Zmiri-data-race-detector"
```

### 实际示例

```rust
// 问题代码：未对齐访问
unsafe fn read_unaligned_ptr() {
    let ptr = 0x1001 as *const u32;
    let _val = *ptr;  // UB: 未对齐
}

// Miri报告：
// error: Undefined Behavior: accessing memory with alignment 1,
//        but alignment 4 is required

// 修复：使用read_unaligned
unsafe fn read_aligned() {
    let ptr = 0x1001 as *const u32;
    let _val = ptr.read_unaligned();  // OK
}

// 问题代码：使用已释放内存
fn use_after_free() {
    let ptr = {
        let local = 5;
        &local as *const i32
    };
    unsafe {
        let _val = *ptr;  // UB: use-after-free
    }
}

// Miri报告：
// error: Undefined Behavior: pointer to alloc1496 was dereferenced
//        after this allocation had already been freed
```

### 在CI中集成Miri

```yaml
# .github/workflows/miri.yml
name: Miri

on: [push, pull_request]

jobs:
  miri:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Miri
        run: |
          rustup component add miri
          cargo miri setup

      - name: Test with Miri
        run: cargo miri test
        env:
          MIRIFLAGS: -Zmiri-strict-provenance
```

---

## Kani模型检查

### 基础概念

Kani使用有界模型检查(BMC)验证Rust代码属性。它将代码转换为逻辑公式，使用SAT/SMT求解器验证。

### 安装与配置

```bash
# 安装
cargo install --locked kani-verifier
kani-setup

# 验证安装
kani --version
```

### 基本证明

```rust
// 简单函数验证
fn add(a: u32, b: u32) -> u32 {
    a + b
}

#[kani::proof]
fn verify_add() {
    let a: u32 = kani::any();  // 任意值
    let b: u32 = kani::any();

    // 假设前提条件
    kani::assume(a < 1000);
    kani::assume(b < 1000);

    let result = add(a, b);

    // 验证后置条件
    assert!(result >= a);  // 单调性
    assert!(result >= b);
    assert_eq!(result, a + b);
}
```

### 复杂验证示例

```rust
/// 二分查找验证
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    while left < right {
        let mid = left + (right - left) / 2;
        match arr[mid].cmp(&target) {
            std::cmp::Ordering::Equal => return Some(mid),
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid,
        }
    }
    None
}

#[kani::proof]
#[kani::unwind(10)]  // 限制循环展开
fn verify_binary_search() {
    // 创建任意数组（已排序）
    let arr: [i32; 5] = kani::any();
    kani::assume(arr[0] <= arr[1]);
    kani::assume(arr[1] <= arr[2]);
    kani::assume(arr[2] <= arr[3]);
    kani::assume(arr[3] <= arr[4]);

    let target: i32 = kani::any();

    let result = binary_search(&arr, target);

    // 验证：如果返回Some(i)，则arr[i] == target
    if let Some(i) = result {
        assert_eq!(arr[i], target);
    }

    // 验证：如果返回None，则target不在数组中
    if result.is_none() {
        assert!(!arr.contains(&target));
    }
}
```

### 不安全代码验证

```rust
/// 安全包装：验证unsafe代码
pub fn safe_slice_access(data: &[u8], index: usize) -> Option<u8> {
    data.get(index).copied()
}

#[kani::proof]
fn verify_safe_access() {
    // 任意字节数组
    let data: [u8; 10] = kani::any();
    let index: usize = kani::any();

    // 验证永远不会panic
    let _result = safe_slice_access(&data, index);

    // 如果返回Some，索引必须在范围内
    if let Some(val) = safe_slice_access(&data, index) {
        assert!(index < data.len());
        assert_eq!(val, data[index]);
    }
}
```

### Kani高级特性

```rust
// 循环展开控制
#[kani::unwind(20)]
#[kani::proof]
fn verify_with_loop() {
    for i in 0..kani::any::<usize>() % 20 {
        // ...
    }
}

// 覆盖率检查
#[kani::proof]
#[kani::should_panic]  // 期望这个证明失败
fn verify_panic_case() {
    let x: u32 = kani::any();
    kani::assume(x > 100);
    assert!(x < 50);  // 应该失败
}

// 使用stub替换复杂函数
mod stubs {
    pub fn complex_external(x: i32) -> i32 {
        kani::any()
    }
}

#[kani::proof]
#[kani::stub(complex_external, stubs::complex_external)]
fn verify_with_stub() {
    // ...
}
```

---

## Verus定理证明

### 概述

Verus是用于验证Rust程序正确性的工具，基于SMT求解器，支持复杂的不变量和前置/后置条件。

### 安装

```bash
cargo install vargo
git clone https://github.com/verus-lang/verus.git
cd verus/source
cargo build --release
```

### 基本证明

```rust
use vstd::prelude::*;

verus! {
    /// 带规范的函数
    fn binary_search(v: &Vec<u64>, k: u64) -> (r: Option<usize>)
        requires
            forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],  // 已排序
        ensures
            match r {
                Some(i) => v[i as int] == k,  // 找到时正确
                None => forall|i: int| 0 <= i < v.len() ==> v[i] != k,  // 未找到时不存在
            }
    {
        let mut i = 0;
        let mut j = v.len();

        while i < j
            invariant
                0 <= i <= j <= v.len(),
                forall|m: int| 0 <= m < i ==> v[m] < k,
                forall|m: int| j <= m < v.len() ==> v[m] > k,
        {
            let mid = i + (j - i) / 2;
            if v[mid] == k {
                return Some(mid);
            } else if v[mid] < k {
                i = mid + 1;
            } else {
                j = mid;
            }
        }
        None
    }
}
```

### 数据结构验证

```rust
verus! {
    /// 验证的栈实现
    struct Stack<T> {
        data: Vec<T>,
    }

    impl<T> Stack<T> {
        fn new() -> (s: Self)
            ensures s.len() == 0
        {
            Stack { data: Vec::new() }
        }

        fn push(&mut self, value: T)
            ensures self.len() == old(self).len() + 1,
                    self.peek() == Some(value)
        {
            self.data.push(value);
        }

        fn pop(&mut self) -> (v: Option<T>)
            requires self.len() > 0
            ensures
                match v {
                    Some(val) => {
                        self.len() == old(self).len() - 1
                    },
                    None => self.len() == old(self).len(),
                }
        {
            self.data.pop()
        }

        fn peek(&self) -> (v: Option<&T>)
            ensures
                match v {
                    Some(val) => self.len() > 0,
                    None => self.len() == 0,
                }
        {
            self.data.last()
        }

        fn len(&self) -> usize {
            self.data.len()
        }
    }
}
```

---

## 验证策略

### 分层验证方法

```
Level 1: 类型系统 (编译器)
├── 所有权检查
├── 借用检查
├── 生命周期验证
└── 零成本

Level 2: 静态分析 (Clippy)
├── 代码质量
├── 常见错误模式
└── 快速反馈

Level 3: 运行时检测 (Miri)
├── UB检测
├── 内存模型验证
└── 开发时检查

Level 4: 模型检查 (Kani)
├── 安全属性
├── 有界验证
└── CI集成

Level 5: 定理证明 (Verus)
├── 功能正确性
├── 复杂不变量
└── 关键组件
```

### 验证投资回报率

| 验证级别 | 投入 | 收益 | 适用场景 |
|----------|------|------|----------|
| 类型系统 | 低 | 高 | 所有代码 |
| 静态分析 | 低 | 中 | 所有代码 |
| Miri | 中 | 高 | unsafe代码 |
| Kani | 中 | 高 | 关键函数 |
| Verus | 高 | 很高 | 核心算法 |

---

## 实战案例

### 案例1: 安全关键状态机

```rust
use kani::proof;

/// 验证状态机转换正确性
#[derive(Debug, Clone, Copy, PartialEq)]
enum State {
    Init,
    Running,
    Error,
    Shutdown,
}

struct StateMachine {
    state: State,
    counter: u32,
}

impl StateMachine {
    fn new() -> Self {
        Self {
            state: State::Init,
            counter: 0,
        }
    }

    fn transition(&mut self, event: Event) -> Result<(), Error> {
        match (self.state, event) {
            (State::Init, Event::Start) => {
                self.state = State::Running;
                Ok(())
            }
            (State::Running, Event::Tick) => {
                self.counter += 1;
                if self.counter > 100 {
                    self.state = State::Error;
                }
                Ok(())
            }
            (State::Running, Event::Stop) => {
                self.state = State::Shutdown;
                Ok(())
            }
            (State::Error, Event::Reset) => {
                self.state = State::Init;
                self.counter = 0;
                Ok(())
            }
            _ => Err(Error::InvalidTransition),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum Event {
    Start,
    Tick,
    Stop,
    Reset,
}

enum Error {
    InvalidTransition,
}

#[proof]
fn verify_state_machine() {
    let mut sm = StateMachine::new();
    assert_eq!(sm.state, State::Init);

    // 验证: Init + Start -> Running
    sm.transition(Event::Start).unwrap();
    assert_eq!(sm.state, State::Running);

    // 验证: 无效转换返回错误
    assert!(sm.transition(Event::Start).is_err());

    // 验证: 100次Tick后进入Error
    for _ in 0..100 {
        sm.transition(Event::Tick).unwrap();
    }
    assert_eq!(sm.state, State::Error);
}
```

### 案例2: 加密算法验证

```rust
/// 验证常量时间比较（防时序攻击）
fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }

    let mut result: u8 = 0;
    for i in 0..a.len() {
        result |= a[i] ^ b[i];
    }

    result == 0
}

#[kani::proof]
fn verify_constant_time() {
    let a: [u8; 32] = kani::any();
    let b: [u8; 32] = kani::any();

    let result = constant_time_eq(&a, &b);

    // 验证：相等时返回true
    if a == b {
        assert!(result);
    }

    // 验证：不等时可能返回false
    // 注意：由于哈希碰撞，不同输入也可能返回true（概率极低）
}
```

---

## 最佳实践

### 1. 从简单开始

```rust
// 先验证简单属性
#[kani::proof]
fn verify_simple_property() {
    let x: u32 = kani::any();
    assert!(x == x);  // 恒真
}
```

### 2. 逐步增加复杂度

```rust
// 添加前提条件
#[kani::proof]
fn verify_with_assumptions() {
    let x: u32 = kani::any();
    kani::assume(x < 100);  // 限制范围

    let result = x * 2;
    assert!(result < 200);
}
```

### 3. 处理循环

```rust
#[kani::proof]
#[kani::unwind(10)]  // 明确指定循环界限
fn verify_with_loop() {
    let n: usize = kani::any();
    kani::assume(n < 10);

    let mut sum = 0;
    for i in 0..n {
        sum += i;
    }

    assert!(sum <= 45);  // 0+1+...+9 = 45
}
```

### 4. 在CI中集成

```yaml
name: Formal Verification

on: [push, pull_request]

jobs:
  kani:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Kani
        run: |
          cargo install --locked kani-verifier
          kani-setup

      - name: Run Kani proofs
        run: cargo kani --workspace

      - name: Run MIRI
        run: |
          rustup component add miri
          cargo miri test
```

---

## 故障排除

### Kani超时

```rust
// 问题：证明超时
#[kani::proof]
fn slow_proof() {
    let x: u64 = kani::any();  // 64位太大
    // ...
}

// 解决：限制输入范围
#[kani::proof]
fn fast_proof() {
    let x: u32 = kani::any();  // 使用32位
    kani::assume(x < 1000);    // 限制范围
    // ...
}
```

### Miri堆溢出

```bash
# 增加Miri栈大小
MIRIFLAGS="-Zmiri-stack-frame=16777216" cargo miri test
```

---

**文档版本**: 1.0
**最后更新**: 2026-03-18
**基于**: Kani 0.40, Miri latest, Verus 0.1
