# Rust安全关键编码规范

## 概述

本文档定义安全关键Rust项目的编码规范，确保代码安全、可靠、可维护，符合ISO 26262 ASIL D、IEC 61508 SIL 4等标准要求。

---

## 1. 安全编码原则

### 1.1 核心原则

```
原则1: 利用Rust类型系统
- 让编译器捕获错误
- 使用类型状态模式
- 零成本抽象优先

原则2: 最小化unsafe代码
- unsafe代码需论证必要性
- 100%代码审查
- Miri验证通过

原则3: 显式优于隐式
- 错误显式处理
- 生命周期显式标注
- 边界检查显式

原则4: 不可变优先
- 默认使用不可变引用
- 内部可变性交待清晰
- 共享状态最小化
```

### 1.2 安全等级对应规范

| 等级 | unsafe代码 | 形式化验证 | 覆盖率 | 审查 |
|------|------------|------------|--------|------|
| ASIL D/SIL 4 | 禁止 | 强制 | MC/DC 100% | 强制双人 |
| ASIL C/SIL 3 | 最小化 | 推荐 | 分支 100% | 强制单人 |
| ASIL B/SIL 2 | 受限 | 可选 | 语句 100% | 抽样 |
| ASIL A/SIL 1 | 规范 | 可选 | 语句 80% | 自检 |
| QM | 规范 | 可选 | 无要求 | 自检 |

---

## 2. 内存安全规范

### 2.1 所有权与借用

**必须 (MUST)**:

```rust
// ✅ 编译器强制执行所有权
let data = vec![1, 2, 3];
let ref1 = &data;     // 不可变借用
let ref2 = &data;     // 多个不可变借用OK
println!("{:?} {:?}", ref1, ref2);
// 借用在这里结束

// ✅ 显式生命周期
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

**禁止 (MUST NOT)**:

```rust
// ❌ 悬垂引用 - 编译器会拒绝
fn dangle() -> &String {
    let s = String::from("hello");
    &s  // 错误: s在这里被释放
}

// ❌ 可变与不可变借用冲突
let mut data = vec![1, 2, 3];
let ref1 = &data;
let ref2 = &mut data;  // 错误: 不能同时存在
println!("{}", ref1[0]);
```

### 2.2 生命周期管理

**推荐 (SHOULD)**:

```rust
// ✅ 显式生命周期注解
struct Parser<'a> {
    input: &'a str,
    position: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Self { input, position: 0 }
    }

    fn peek(&self) -> Option<&'a str> {
        self.input.get(self.position..)
    }
}
```

**避免 (SHOULD NOT)**:

```rust
// ❌ 隐式生命周期
struct BadParser {
    input: &str,  // 缺少显式生命周期
}
```

### 2.3 智能指针使用

**必须 (MUST)**:

```rust
// ✅ 使用Box进行堆分配
let data = Box::new([0u8; 1024]);

// ✅ 使用Rc/Arc进行共享所有权
use std::sync::Arc;
let shared = Arc::new(config);
let clone1 = Arc::clone(&shared);
let clone2 = Arc::clone(&shared);

// ✅ 使用RefCell进行内部可变性
use std::cell::RefCell;
let data = RefCell::new(0);
*data.borrow_mut() += 1;
```

**警告 (WARNING)**:

```rust
// ⚠️ RefCell运行时检查
let data = RefCell::new(0);
let _ref1 = data.borrow();
let _ref2 = data.borrow_mut();  // 运行时panic!

// ⚠️ 循环引用风险
use std::rc::{Rc, Weak};
use std::cell::RefCell;

struct Node {
    value: i32,
    parent: RefCell<Weak<Node>>,  // ✅ 使用Weak打破循环
    children: RefCell<Vec<Rc<Node>>>,
}
```

---

## 3. unsafe代码规范

### 3.1 使用准则

**ASIL D/SIL 4: 完全禁止unsafe**

**ASIL C及以下: 严格受限**

```rust
// ✅ 格式化的unsafe块
/// # Safety
///
/// 调用者必须确保:
/// - `ptr` 是非空的有效指针
/// - `ptr` 指向已分配的内存
/// - 内存对齐满足T的要求
/// - 内存未被其他引用可变借用
pub unsafe fn read_value<T>(ptr: *const T) -> T {
    // SAFETY: 调用者已确保所有前提条件
    ptr.read()
}
```

### 3.2 必需文档

```rust
/// 从原始指针读取值
///
/// # Safety
///
/// 调用此函数是unsafe的，因为需要满足以下条件:
///
/// 1. `ptr` 必须是非空的有效指针
/// 2. `ptr` 必须正确对齐
/// 3. `ptr` 必须指向已初始化的内存
/// 4. 返回的引用必须遵守Rust的别名规则
///
/// 违反这些条件会导致未定义行为。
///
/// # Examples
///
/// ```
/// let value = 42;
/// let ptr = &value as *const i32;
/// unsafe {
///     assert_eq!(safe_read(ptr), 42);
/// }
/// ```
///
/// # Invariants
///
/// - 此函数不会释放内存
/// - 不会创建悬垂指针
/// - 遵守Rust内存模型
unsafe fn safe_read<T>(ptr: *const T) -> T
where
    T: Copy,
{
    std::ptr::read(ptr)
}
```

### 3.3 常见模式

**安全包装器模式**:

```rust
/// 安全的切片访问包装器
pub struct SafeSlice<T> {
    ptr: *const T,
    len: usize,
}

impl<T> SafeSlice<T> {
    /// 从切片创建 (安全)
    pub fn from_slice(slice: &[T]) -> Self {
        Self {
            ptr: slice.as_ptr(),
            len: slice.len(),
        }
    }

    /// 安全索引访问
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len {
            // SAFETY: 边界检查通过
            Some(unsafe { &*self.ptr.add(index) })
        } else {
            None
        }
    }

    /// 长度获取
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}
```

---

## 4. 并发安全规范

### 4.1 线程安全类型

**必须 (MUST)**:

```rust
use std::sync::{Arc, Mutex, RwLock};
use std::thread;

// ✅ 使用Arc共享所有权
let data = Arc::new(Mutex::new(0));
let mut handles = vec![];

for _ in 0..10 {
    let data = Arc::clone(&data);
    let handle = thread::spawn(move || {
        let mut num = data.lock().unwrap();
        *num += 1;
    });
    handles.push(handle);
}

for handle in handles {
    handle.join().unwrap();
}

assert_eq!(*data.lock().unwrap(), 10);
```

**禁止 (MUST NOT)**:

```rust
// ❌ 非Send类型跨线程
use std::rc::Rc;

let data = Rc::new(0);
thread::spawn(move || {
    println!("{}", data);  // 编译错误: Rc不是Send
});
```

### 4.2 同步原语

**推荐 (SHOULD)**:

```rust
use std::sync::{Mutex, RwLock, Condvar};

// ✅ 细粒度锁
struct ThreadSafeData {
    config: RwLock<Config>,     // 多读少写
    state: Mutex<State>,        // 频繁修改
    cond: Condvar,              // 条件通知
}

// ✅ 锁保护最小范围
impl ThreadSafeData {
    fn update_state(&self, new_state: State) {
        let mut state = self.state.lock().unwrap();
        *state = new_state;
        self.cond.notify_all();
    }  // 锁在这里自动释放
}
```

**避免 (SHOULD NOT)**:

```rust
// ❌ 锁粒度太大
struct BadDesign {
    data: Mutex<AllData>,  // 一个大锁
}

// ❌ 死锁风险
fn deadlock_risk(a: &Mutex<i32>, b: &Mutex<i32>) {
    let _guard1 = a.lock().unwrap();
    let _guard2 = b.lock().unwrap();  // 如果另一个线程相反顺序获取锁...
}
```

### 4.3 异步代码

**必须 (MUST)**:

```rust
use tokio::sync::Mutex;  // 异步锁

// ✅ 异步锁用于异步上下文
async fn async_update(data: &Mutex<Data>) {
    let mut guard = data.lock().await;
    guard.process().await;
}  // 锁在这里释放

// ✅ 使用channel通信
tokio::spawn(async move {
    while let Some(msg) = rx.recv().await {
        process(msg).await;
    }
});
```

---

## 5. 错误处理规范

### 5.1 Result和Option

**必须 (MUST)**:

```rust
use std::fs::File;
use std::io::{self, Read};

// ✅ 使用?传播错误
fn read_config(path: &str) -> io::Result<String> {
    let mut file = File::open(path)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok(contents)
}

// ✅ 显式处理错误
match operation() {
    Ok(result) => result,
    Err(e) => {
        log::error!("操作失败: {}", e);
        default_value
    }
}

// ✅ Option显式处理
let value = maybe_value
    .ok_or_else(|| Error::ValueMissing)?;
```

**禁止 (MUST NOT)**:

```rust
// ❌ 忽略错误
let _ = file.write_all(data);  // 错误被忽略!

// ❌ 使用unwrap/expect
let file = File::open("config.txt").unwrap();  // 可能panic!

// ❌ 不处理Option
let value = maybe_value.unwrap();  // 可能panic!
```

### 5.2 自定义错误类型

```rust
use std::fmt;
use std::error::Error;

/// 安全关键应用错误类型
#[derive(Debug)]
pub enum SafetyError {
    /// 配置错误
    Config { source: ConfigError, path: String },
    /// 通信错误
    Communication { source: io::Error, endpoint: String },
    /// 协议错误
    Protocol { code: u16, message: String },
    /// 安全违规
    Security { violation: SecurityViolation },
}

impl fmt::Display for SafetyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SafetyError::Config { source, path } => {
                write!(f, "配置错误在 '{}': {}", path, source)
            }
            SafetyError::Communication { source, endpoint } => {
                write!(f, "通信错误与 '{}': {}", endpoint, source)
            }
            SafetyError::Protocol { code, message } => {
                write!(f, "协议错误 [{}]: {}", code, message)
            }
            SafetyError::Security { violation } => {
                write!(f, "安全违规: {:?}", violation)
            }
        }
    }
}

impl Error for SafetyError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            SafetyError::Config { source, .. } => Some(source),
            SafetyError::Communication { source, .. } => Some(source),
            _ => None,
        }
    }
}
```

### 5.3 错误转换

```rust
use thiserror::Error;

/// 使用thiserror简化错误定义
#[derive(Error, Debug)]
pub enum AppError {
    #[error("IO错误: {0}")]
    Io(#[from] io::Error),

    #[error("解析错误: {message}")]
    Parse { message: String },

    #[error("验证失败: {field} = {value}")]
    Validation { field: String, value: String },
}

/// 使用anyhow简化应用代码
use anyhow::{Context, Result};

fn load_data(path: &str) -> Result<Data> {
    let contents = fs::read_to_string(path)
        .with_context(|| format!("读取文件失败: {}", path))?;

    let data: Data = serde_json::from_str(&contents)
        .context("解析JSON失败")?;

    Ok(data)
}
```

---

## 6. 嵌入式特定规范

### 6.1 no_std环境

```rust
#![no_std]  // 禁止标准库
#![no_main] // 禁用标准入口点

use core::panic::PanicInfo;

// ✅ 自定义panic处理器
#[cfg(not(test))]
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    // 记录panic信息
    // 进入安全状态
    loop {
        cortex_m::asm::bkpt();
    }
}

// ✅ 使用core库
use core::slice;
use core::ptr;
use core::mem::MaybeUninit;

// ✅ 静态分配
static mut BUFFER: [u8; 1024] = [0; 1024];

// ✅ MaybeUninit用于未初始化内存
let mut uninit: MaybeUninit<Data> = MaybeUninit::uninit();
let ptr = uninit.as_mut_ptr();
// SAFETY: 初始化内存
unsafe { ptr.write(Data::new()) };
let data = unsafe { uninit.assume_init() };
```

### 6.2 硬件抽象

```rust
/// 寄存器访问 (使用svd2rust生成)
use stm32f4::stm32f407::Peripherals;

fn configure_gpio(dp: &Peripherals) {
    // ✅ 类型安全的寄存器访问
    dp.GPIOA.moder.modify(|_, w| {
        w.moder5().output()  // PA5 输出模式
    });

    dp.GPIOA.odr.modify(|_, w| {
        w.odr5().set_bit()  // 设置PA5高电平
    });
}

/// 手动MMIO (unsafe必要)
const GPIOA_ODR: *mut u32 = 0x4002_0014 as *mut u32;

unsafe fn set_pa5() {
    // SAFETY: 正确地址，原子操作
    core::ptr::write_volatile(GPIOA_ODR, 1 << 5);
}
```

---

## 7. 测试规范

### 7.1 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    // ✅ 边界条件测试
    #[test]
    fn test_boundaries() {
        assert_eq!(calculate(0), 0);
        assert_eq!(calculate(1), 1);
        assert_eq!(calculate(u32::MAX), expected_max);
    }

    // ✅ 错误条件测试
    #[test]
    fn test_error_conditions() {
        let result = parse_int("not a number");
        assert!(result.is_err());
    }

    // ✅ 属性测试 (使用proptest)
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_addition_commutative(a: i32, b: i32) {
            prop_assert_eq!(add(a, b), add(b, a));
        }
    }
}
```

### 7.2 集成测试

```rust
// tests/integration_test.rs
use my_crate::SafetySystem;

#[test]
fn test_safety_system_end_to_end() {
    let mut system = SafetySystem::new();

    // 正常操作
    system.initialize().expect("初始化失败");
    let result = system.process(Input::Normal);
    assert!(result.is_ok());

    // 故障注入
    system.inject_fault(Fault::SensorError);
    let result = system.process(Input::Normal);
    assert!(matches!(result, Err(SafetyError::FaultDetected)));

    // 安全状态验证
    assert!(system.is_in_safe_state());
}
```

### 7.3 文档测试

```rust
/// 计算安全检查
///
/// # Examples
///
/// ```
/// use safety_critical::safety_check;
///
/// assert!(safety_check(100));
/// assert!(!safety_check(0));
/// ```
pub fn safety_check(value: u32) -> bool {
    value > 0
}
```

---

## 8. 代码度量标准

### 8.1 复杂度限制

| 度量 | 最大值 | 警告 | ASIL D要求 |
|------|--------|------|------------|
| 圈复杂度 | 10 | 15 | <=10 |
| 认知复杂度 | 15 | 20 | <=15 |
| 函数行数 | 50 | 75 | <=50 |
| 参数数量 | 5 | 7 | <=5 |
| 嵌套深度 | 3 | 4 | <=3 |

### 8.2 覆盖率要求

| 等级 | 语句 | 分支 | MC/DC | 函数 |
|------|------|------|-------|------|
| ASIL D | 100% | 100% | 100% | 100% |
| ASIL C | 100% | 100% | - | 100% |
| ASIL B | 100% | 90% | - | 100% |
| ASIL A | 90% | 80% | - | 100% |

---

## 9. 注释与文档

### 9.1 文档注释

```rust
/// 安全关键传感器读取
///
/// 从指定传感器读取值，进行范围检查和安全验证。
///
/// # Arguments
///
/// * `sensor_id` - 传感器标识符 (1-32)
/// * `timeout_ms` - 超时时间 (毫秒)
///
/// # Returns
///
/// * `Ok(SensorValue)` - 成功读取的有效值
/// * `Err(SensorError::InvalidId)` - 传感器ID无效
/// * `Err(SensorError::Timeout)` - 读取超时
/// * `Err(SensorError::OutOfRange)` - 值超出安全范围
///
/// # Examples
///
/// ```
/// use safety_critical::read_sensor;
///
/// match read_sensor(1, 100) {
///     Ok(value) => println!("传感器值: {}", value),
///     Err(e) => eprintln!("读取失败: {}", e),
/// }
/// ```
///
/// # Safety
///
/// 此函数不会panic，所有错误都通过Result返回。
/// 超时机制确保函数不会无限期阻塞。
pub fn read_sensor(sensor_id: u8, timeout_ms: u32) -> Result<SensorValue, SensorError> {
    // 实现...
}
```

### 9.2 实现注释

```rust
fn complex_algorithm(input: &[u8]) -> Result<Output, Error> {
    // 步骤1: 验证输入长度
    if input.len() < MIN_LENGTH {
        return Err(Error::InputTooShort);
    }

    // 步骤2: 计算校验和
    // 使用 wrapping_add 避免溢出panic
    let checksum = input.iter().fold(0u8, |acc, &b| acc.wrapping_add(b));

    // 步骤3: 验证校验和
    // 注意: 最后一个字节是校验和
    if checksum != input[input.len() - 1] {
        return Err(Error::ChecksumMismatch);
    }

    // 继续处理...
}
```

---

**文档版本**: 1.0
**最后更新**: 2026-03-18
**适用标准**: ISO 26262:2018, IEC 61508:2010

---

*所有开发人员必须遵守此规范，审查时作为检查依据。*
