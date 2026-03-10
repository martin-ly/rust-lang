# Panic-Probe 与嵌入式 Panic 处理形式化分析

> **主题**: 嵌入式Panic处理机制与调试输出
>
> **形式化框架**: 错误恢复 + 调试输出 + 探针协议
>
> **参考**: knurling-rs tools, ARM Cortex-M Fault Handling

---

## 目录

- [Panic-Probe 与嵌入式 Panic 处理形式化分析](#panic-probe-与嵌入式-panic-处理形式化分析)
  - [目录](#目录)
  - [1. 项目概览与解决的问题](#1-项目概览与解决的问题)
    - [1.1 嵌入式系统的故障处理挑战](#11-嵌入式系统的故障处理挑战)
    - [1.2 Panic的语义与要求](#12-panic的语义与要求)
    - [1.3 Panic-Probe的设计目标](#13-panic-probe的设计目标)
  - [2. 核心概念与技术原理](#2-核心概念与技术原理)
    - [2.1 Rust Panic机制](#21-rust-panic机制)
    - [2.2 Panic处理器类型](#22-panic处理器类型)
    - [2.3 RTT (Real-Time Transfer) 协议](#23-rtt-real-time-transfer-协议)
    - [2.4 探针通信机制](#24-探针通信机制)
    - [2.5 栈回溯原理](#25-栈回溯原理)
  - [3. Trait设计与类型系统运用](#3-trait设计与类型系统运用)
    - [3.1 PanicInfo结构](#31-panicinfo结构)
    - [3.2 PanicHandler特性](#32-panichandler特性)
    - [3.3 Defmt集成](#33-defmt集成)
    - [3.4 探针协议抽象](#34-探针协议抽象)
  - [4. 使用场景与实际案例](#4-使用场景与实际案例)
    - [4.1 开发调试场景](#41-开发调试场景)
    - [4.2 生产环境处理](#42-生产环境处理)
    - [4.3 故障记录与恢复](#43-故障记录与恢复)
    - [4.4 远程诊断](#44-远程诊断)
    - [4.5 安全关键系统](#45-安全关键系统)
  - [5. 与其他方案的对比](#5-与其他方案的对比)
    - [5.1 与Semihosting的对比](#51-与semihosting的对比)
    - [5.2 与ITM/SWO的对比](#52-与itmswo的对比)
    - [5.3 与UART输出的对比](#53-与uart输出的对比)
  - [6. 完整代码示例](#6-完整代码示例)
    - [6.1 完整调试配置](#61-完整调试配置)
    - [6.2 自定义Panic处理器](#62-自定义panic处理器)
    - [6.3 故障日志系统](#63-故障日志系统)
    - [6.4 多级恢复策略](#64-多级恢复策略)
  - [7. 性能分析](#7-性能分析)
    - [7.1 Panic处理延迟](#71-panic处理延迟)
    - [7.2 代码大小开销](#72-代码大小开销)
    - [7.3 运行时开销](#73-运行时开销)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 Panic处理器选择](#81-panic处理器选择)
    - [8.2 调试信息配置](#82-调试信息配置)
    - [8.3 故障恢复模式](#83-故障恢复模式)
    - [8.4 安全考虑](#84-安全考虑)
  - [9. 形式化定理与证明](#9-形式化定理与证明)
    - [9.1 Panic不返回定理](#91-panic不返回定理)
    - [9.2 探针非侵入性定理](#92-探针非侵入性定理)
    - [9.3 栈回溯完整性定理](#93-栈回溯完整性定理)
  - [10. 反例与边界情况](#10-反例与边界情况)
    - [10.1 堆栈溢出](#101-堆栈溢出)
    - [10.2 双重Panic](#102-双重panic)
    - [10.3 硬件故障](#103-硬件故障)

---

## 1. 项目概览与解决的问题

### 1.1 嵌入式系统的故障处理挑战

嵌入式系统与传统桌面/服务器环境有本质差异：

**资源受限环境**：

- 无MMU（内存管理单元）：无法使用虚拟内存保护
- 有限RAM：通常几KB到几百KB
- 无stdout/stderr：传统错误输出不可用
- 可能无屏幕：无法显示错误信息

**可靠性要求**：

- 7x24运行：不能简单崩溃退出
- 安全关键：故障必须安全处理
- 远程部署：无法物理访问调试

```rust
// 桌面环境：可以简单panic并退出
fn main() {
    let result = risky_operation();
    // 如果失败，panic，程序退出
}

// 嵌入式环境：必须安全处理
#[entry]
fn main() -> ! {
    loop {
        match risky_operation() {
            Ok(result) => process(result),
            Err(e) => {
                // 不能简单退出！
                // 必须：记录错误、进入安全状态、可能重启
                handle_error_safely(e);
            }
        }
    }
}
```

### 1.2 Panic的语义与要求

Rust的panic机制：

```rust
// Panic展开(unwinding) vs 中止(abort)
// 嵌入式通常使用abort，因为：
// 1. 无 unwinding 表（节省代码空间）
// 2. 更简单，无运行时开销
// 3. 符合嵌入式可靠性要求

#[cfg(panic = "abort")]
fn panic_handler(info: &PanicInfo) -> ! {
    // 永不返回
    loop {}
}
```

**Panic处理器要求**：

1. **发散类型**：返回类型为 `!` (never type)
2. **单一实例**：全局只能有一个panic处理器
3. **最小依赖**：不能使用可能panic的代码
4. **快速执行**：通常在中断禁用状态执行

### 1.3 Panic-Probe的设计目标

panic-probe 提供：

1. **调试输出**：通过调试探针输出panic信息
2. **栈回溯**：捕获和传输调用栈
3. **与非侵入性调试**：不干扰正常执行
4. **Defmt集成**：压缩日志格式支持
5. **可配置策略**：根据环境选择不同行为

```rust
// 典型配置
[dependencies]
panic-probe = { version = "0.3", features = ["print-defmt"] }
defmt = "0.3"
defmt-rtt = "0.4"

// 代码中使用
use panic_probe as _;

#[entry]
fn main() -> ! {
    defmt::info!("Starting...");

    // 如果panic，自动通过probe输出信息
    assert!(critical_check());

    loop {}
}
```

---

## 2. 核心概念与技术原理

### 2.1 Rust Panic机制

```rust
// Panic流程
pub fn panic_impl(info: &PanicInfo) -> ! {
    // 1. 禁用中断（防止嵌套panic）
    cortex_m::interrupt::disable();

    // 2. 输出panic信息
    report_panic(info);

    // 3. 执行终止策略
    abort();
}

// 三种中止方式
enum AbortStrategy {
    InfiniteLoop,   // 进入无限循环（调试）
    Reset,          // 系统复位（恢复）
    HardFault,      // 触发HardFault（调试器捕获）
}
```

### 2.2 Panic处理器类型

| 处理器 | 行为 | 适用场景 | 代码大小 |
|-------|------|---------|---------|
| `panic-halt` | 无限循环 | 最小代码、生产 | ~100B |
| `panic-reset` | 系统复位 | 自动恢复 | ~200B |
| `panic-probe` | RTT输出 | 调试开发 | ~1KB |
| `panic-semihosting` | 半主机输出 | 仿真 | ~2KB |
| `panic-itm` | ITM输出 | 跟踪调试 | ~500B |

```rust
// panic-halt 实现
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {
        cortex_m::asm::wfi();  // 等待中断，节能
    }
}

// panic-reset 实现
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    cortex_m::peripheral::SCB::sys_reset();
}

// panic-probe 实现
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    cortex_m::interrupt::disable();

    // 通过RTT输出
    defmt::error!("PANIC: {}", info.message());
    if let Some(loc) = info.location() {
        defmt::error!("at {}:{}", loc.file(), loc.line());
    }

    // 触发断点供调试器捕获
    cortex_m::asm::bkpt();

    loop {}
}
```

### 2.3 RTT (Real-Time Transfer) 协议

RTT是SEGGER开发的实时传输协议：

```
内存布局:
┌─────────────────────────────────────┐
│           Control Block              │
│  (ID, UpBufferCount, DownBufferCount)│
├─────────────────────────────────────┤
│           Up Buffer 0                │
│  (Target -> Host, 日志输出)          │
├─────────────────────────────────────┤
│           Down Buffer 0              │
│  (Host -> Target, 命令输入)          │
└─────────────────────────────────────┘
```

**工作原理**：

1. 目标设备将数据写入环形缓冲区
2. 调试探针轮询/中断读取缓冲区
3. 无需目标CPU参与数据传输
4. 支持多通道（日志、命令、数据）

```rust
// RTT通道定义
struct RttChannel {
    name: *const u8,
    buffer: *mut u8,
    size: usize,
    write_off: AtomicUsize,
    read_off: AtomicUsize,
    flags: AtomicU32,
}

// 写入操作（目标端）
fn write(channel: &mut RttChannel, data: &[u8]) {
    let write_pos = channel.write_off.load(Ordering::Relaxed);
    let read_pos = channel.read_off.load(Ordering::Acquire);

    let available = if write_pos >= read_pos {
        channel.size - write_pos + read_pos - 1
    } else {
        read_pos - write_pos - 1
    };

    if data.len() > available {
        // 缓冲区满，丢弃或阻塞
        return;
    }

    // 写入数据
    let wrap_size = channel.size - write_pos;
    if data.len() <= wrap_size {
        // 单次写入
        unsafe {
            core::ptr::copy_nonoverlapping(
                data.as_ptr(),
                channel.buffer.add(write_pos),
                data.len()
            );
        }
    } else {
        // 环绕写入
        unsafe {
            core::ptr::copy_nonoverlapping(
                data.as_ptr(),
                channel.buffer.add(write_pos),
                wrap_size
            );
            core::ptr::copy_nonoverlapping(
                data.as_ptr().add(wrap_size),
                channel.buffer,
                data.len() - wrap_size
            );
        }
    }

    // 更新写指针
    channel.write_off.store(
        (write_pos + data.len()) % channel.size,
        Ordering::Release
    );
}
```

### 2.4 探针通信机制

```
目标设备 <-> 调试探针 <-> 主机

1. 目标写入RTT缓冲区（内存操作）
2. 探针通过SWD/JTAG读取内存
3. 探针通过USB将数据传输到主机
4. 主机应用程序显示/记录日志

优势:
- 无需额外硬件（使用调试接口）
- 不影响目标执行（轮询模式）
- 高带宽（可达数MB/s）
```

### 2.5 栈回溯原理

栈回溯（Stack Unwinding）在panic时捕获调用链：

```rust
// Cortex-M栈回溯
struct StackFrame {
    r0: u32,
    r1: u32,
    r2: u32,
    r3: u32,
    r12: u32,
    lr: u32,   // 链接寄存器（返回地址）
    pc: u32,   // 程序计数器
    xpsr: u32, // 程序状态寄存器
}

fn capture_stack_trace() -> Vec<StackFrame, 32> {
    let mut frames = Vec::new();

    // 获取当前栈指针
    let sp: u32;
    unsafe { asm!("mov {}, sp", out(reg) sp); }

    // 遍历栈帧
    let mut fp = get_frame_pointer();
    while fp != 0 && frames.len() < 32 {
        unsafe {
            let frame = *(fp as *const StackFrame);
            frames.push(frame).ok();
            fp = *(fp as *const u32).offset(-2); // 上一个帧指针
        }
    }

    frames
}

// 符号解析（主机端）
fn resolve_symbol(pc: u32, elf: &Elf) -> Option<String> {
    // 查找ELF符号表
    elf.symbols
        .iter()
        .find(|s| s.address <= pc && pc < s.address + s.size)
        .map(|s| s.name.clone())
}
```

---

## 3. Trait设计与类型系统运用

### 3.1 PanicInfo结构

```rust
// 标准库PanicInfo
pub struct PanicInfo<'a> {
    payload: &'a (dyn Any + Send),
    message: Option<&'a fmt::Arguments<'a>>,
    location: Option<&'a Location<'a>>,
    can_unwind: bool,
}

impl<'a> PanicInfo<'a> {
    pub fn message(&self) -> Option<&fmt::Arguments> {
        self.message
    }

    pub fn location(&self) -> Option<&Location> {
        self.location
    }

    pub fn payload(&self) -> &(dyn Any + Send) {
        self.payload
    }
}

pub struct Location<'a> {
    file: &'a str,
    line: u32,
    col: u32,
}

impl<'a> Location<'a> {
    pub fn file(&self) -> &str { self.file }
    pub fn line(&self) -> u32 { self.line }
    pub fn column(&self) -> u32 { self.col }
}
```

### 3.2 PanicHandler特性

```rust
// Panic处理器trait（概念性）
pub trait PanicHandler {
    // 永不返回
    fn handle(&self, info: &PanicInfo) -> !;
}

// 实际使用：全局函数
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    // 实现必须是发散的
}

// 可配置处理器
pub struct ConfigurablePanic {
    strategy: PanicStrategy,
    pre_hook: Option<fn(&PanicInfo)>,
    post_hook: Option<fn()>,
}

impl ConfigurablePanic {
    pub fn handle(&self, info: &PanicInfo) -> ! {
        // 执行前置钩子
        if let Some(hook) = self.pre_hook {
            hook(info);
        }

        // 执行策略
        match self.strategy {
            PanicStrategy::Halt => self.halt(),
            PanicStrategy::Reset => self.reset(),
            PanicStrategy::Report => self.report(info),
        }

        // 执行后置钩子
        if let Some(hook) = self.post_hook {
            hook();
        }

        // 最终停止
        loop {
            cortex_m::asm::wfi();
        }
    }
}
```

### 3.3 Defmt集成

```rust
// panic-probe与defmt集成
use defmt::error;

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    cortex_m::interrupt::disable();

    // 使用defmt输出（压缩格式）
    if let Some(location) = info.location() {
        error!(
            "PANIC at {}:{}:{}",
            location.file(),
            location.line(),
            location.column()
        );
    }

    if let Some(message) = info.message() {
        error!("Message: {}", message);
    }

    // 捕获栈回溯
    capture_and_log_backtrace();

    // 触发调试断点
    cortex_m::asm::bkpt();

    loop {}
}
```

### 3.4 探针协议抽象

```rust
// 探针通信trait
pub trait ProbeChannel {
    type Error;

    fn write(&mut self, data: &[u8]) -> Result<(), Self::Error>;
    fn flush(&mut self) -> Result<(), Self::Error>;
}

// RTT实现
pub struct RttChannel {
    buffer: &'static mut [u8],
    write_pos: AtomicUsize,
    read_pos: AtomicUsize,
}

impl ProbeChannel for RttChannel {
    type Error = RttError;

    fn write(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        // RTT环形缓冲区写入
        Ok(())
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        // 等待探针读取
        Ok(())
    }
}

// ITM实现（SWO）
pub struct ItmChannel {
    stimulus_port: u32,
}

impl ProbeChannel for ItmChannel {
    type Error = ItmError;

    fn write(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        // ITM FIFO写入
        for &byte in data {
            unsafe {
                core::ptr::write_volatile(
                    (ITM_BASE + self.stimulus_port * 4) as *mut u32,
                    byte as u32
                );
            }
        }
        Ok(())
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        // ITM自动刷新
        Ok(())
    }
}
```

---

## 4. 使用场景与实际案例

### 4.1 开发调试场景

```rust
// 开发配置: panic-probe + defmt
[dependencies]
panic-probe = { version = "0.3", features = ["print-defmt"] }
defmt = "0.3"
defmt-rtt = "0.4"

// 代码
use defmt::*;
use panic_probe as _;

#[entry]
fn main() -> ! {
    info!("Application starting");

    let sensor = Sensor::init();
    assert!(sensor.is_ok(), "Sensor initialization failed");

    loop {
        match read_sensor() {
            Ok(data) => process(data),
            Err(e) => {
                // 如果这里panic，信息会通过probe输出
                panic!("Sensor read failed: {:?}", e);
            }
        }
    }
}

// 调试器输出:
// 0.000000 INFO  Application starting
// 0.001234 INFO  Sensor initialized
// 0.123456 ERROR PANIC at src/main.rs:25:17
// 0.123456 ERROR Message: Sensor read failed: Timeout
// 0.123456 ERROR Stack trace:
//   0: main::read_sensor
//   1: main
```

### 4.2 生产环境处理

```rust
// 生产配置: panic-reset
[dependencies]
panic-reset = "0.1"

// 或使用自定义处理器
use cortex_m::peripheral::SCB;

static PANIC_COUNT: AtomicU32 = AtomicU32::new(0);
const MAX_PANICS: u32 = 3;

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    cortex_m::interrupt::disable();

    // 增加panic计数
    let count = PANIC_COUNT.fetch_add(1, Ordering::SeqCst);

    if count < MAX_PANICS {
        // 短暂延迟后复位（给外部看门狗时间）
        for _ in 0..100000 {
            cortex_m::asm::nop();
        }
        SCB::sys_reset();
    } else {
        // 太多panic，进入安全模式
        enter_safe_mode();
        loop {
            cortex_m::asm::wfi();
        }
    }
}

fn enter_safe_mode() {
    // 关闭所有输出
    disable_outputs();
    // 设置故障指示
    set_error_led();
    // 记录故障信息（如果有持久存储）
    log_failure();
}
```

### 4.3 故障记录与恢复

```rust
use littlefs2::fs::{Filesystem, File, OpenOptions};
use littlefs2::io::Write;

// 持久化panic信息
#[repr(C)]
struct PanicRecord {
    timestamp: u64,
    line: u32,
    file_hash: u32,  // 文件名哈希，节省空间
    message_buffer: [u8; 128],
    message_len: u8,
    stack_hash: u32, // 栈回溯哈希
}

static mut PANIC_STORAGE: Option<PanicStorage> = None;

struct PanicStorage {
    fs: Filesystem<FlashStorage>,
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    cortex_m::interrupt::disable();

    // 尝试记录panic
    unsafe {
        if let Some(ref mut storage) = PANIC_STORAGE {
            let _ = record_panic(storage, info);
        }
    }

    // 复位
    SCB::sys_reset();
}

fn record_panic(storage: &mut PanicStorage, info: &PanicInfo) -> Result<(), Error> {
    let record = PanicRecord {
        timestamp: get_timestamp(),
        line: info.location().map(|l| l.line()).unwrap_or(0),
        file_hash: hash_file(info.location().map(|l| l.file()).unwrap_or("")),
        message_buffer: extract_message(info),
        message_len: 0,
        stack_hash: hash_stack(),
    };

    // 写入文件
    storage.fs.open_file_with_options_and_then(
        |opt| opt.write(true).create(true).append(true),
        "/panics.log",
        |file| {
            let bytes = unsafe {
                core::slice::from_raw_parts(
                    &record as *const _ as *const u8,
                    core::mem::size_of::<PanicRecord>()
                )
            };
            file.write_all(bytes)?;
            file.sync()?;
            Ok(())
        }
    )?;

    Ok(())
}

// 启动时检查之前的panic
fn check_previous_panics(fs: &Filesystem<FlashStorage>) {
    let result = fs.open_file_with_options_and_then(
        |opt| opt.read(true),
        "/panics.log",
        |file| {
            let mut count = 0;
            let mut buffer = [0u8; core::mem::size_of::<PanicRecord>()];

            while file.read(&mut buffer).unwrap_or(0) == buffer.len() {
                let record: &PanicRecord = unsafe {
                    &*(buffer.as_ptr() as *const PanicRecord)
                };
                defmt::warn!("Previous panic at line {}", record.line);
                count += 1;
            }

            Ok(count)
        }
    );

    if let Ok(Ok(count)) = result {
        if count > 0 {
            defmt::info!("Found {} previous panic records", count);
            // 可选择上报或分析
        }
    }
}
```

### 4.4 远程诊断

```rust
// 通过无线连接发送panic信息
use embassy_net::tcp::TcpSocket;

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    cortex_m::interrupt::disable();

    // 尝试发送panic信息
    if network_is_available() {
        let _ = send_panic_report(info);
    }

    // 本地存储备份
    store_panic_locally(info);

    // 复位或停止
    SCB::sys_reset();
}

fn send_panic_report(info: &PanicInfo) -> Result<(), Error> {
    // 构建panic报告
    let report = format_panic_report(info);

    // 发送HTTP POST
    let mut socket = TcpSocket::new(...);
    socket.connect(REMOTE_SERVER)?;

    let request = format!(
        "POST /panic-report HTTP/1.1\r\n\
         Host: {}\r\n\
         Content-Length: {}\r\n\
         \r\n{}",
        REMOTE_SERVER,
        report.len(),
        report
    );

    socket.write_all(request.as_bytes())?;
    socket.flush()?;

    Ok(())
}
```

### 4.5 安全关键系统

```rust
// IEC 61508 / ISO 26262 兼容的panic处理

// 安全状态
enum SafetyState {
    Normal,
    Degraded,
    Safe,
}

static SAFETY_STATE: AtomicU8 = AtomicU8::new(SafetyState::Normal as u8);

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    // 立即进入安全状态
    enter_safe_state();

    // 记录诊断信息
    record_diagnostic(info);

    // 通知安全监控器
    notify_safety_monitor();

    // 根据严重程度处理
    let severity = assess_severity(info);
    match severity {
        Severity::Critical => {
            // 立即切断所有输出
            disable_all_outputs();
            loop { wfi(); }
        }
        Severity::Major => {
            // 尝试安全复位
            perform_safe_reset();
        }
        Severity::Minor => {
            // 记录并继续
            log_and_continue();
        }
    }
}

fn enter_safe_state() {
    SAFETY_STATE.store(SafetyState::Safe as u8, Ordering::SeqCst);

    // 关闭执行器
    disable_actuators();

    // 设置安全输出
    set_safe_outputs();

    // 启动看门狗
    start_watchdog();
}
```

---

## 5. 与其他方案的对比

### 5.1 与Semihosting的对比

| 特性 | Panic-Probe/RTT | Semihosting |
|-----|-----------------|-------------|
| 速度 | ⚡ 快（MB/s） | 🐢 慢（KB/s） |
| 侵入性 | 低 | 高（中断目标） |
| 调试器依赖 | 需要 | 需要 |
| 生产可用 | ✅ 可以 | ❌ 不应该 |
| 代码大小 | 小 | 大 |

```rust
// Semihosting（慢，侵入性）
#[cfg(feature = "semihosting")]
fn panic(info: &PanicInfo) -> ! {
    hprintln!("PANIC: {}", info).unwrap();
    asm::bkpt();
    loop {}
}

// RTT（快，非侵入性）
#[cfg(feature = "rtt")]
fn panic(info: &PanicInfo) -> ! {
    rprintln!("PANIC: {}", info);
    asm::bkpt();
    loop {}
}
```

### 5.2 与ITM/SWO的对比

| 特性 | RTT | ITM/SWO |
|-----|-----|---------|
| 引脚需求 | 调试接口 | 调试接口+SWO |
| 带宽 | 高 | 中 |
| 实时性 | 好 | 极好 |
| 目标CPU开销 | 极低 | 极低 |
| 多核支持 | 是 | 有限 |
| 时间戳 | 软件 | 硬件 |

### 5.3 与UART输出的对比

| 特性 | RTT | UART |
|-----|-----|------|
| 引脚需求 | 调试接口 | 专用UART引脚 |
| 配置复杂度 | 低 | 中 |
| 波特率配置 | 无 | 需要 |
| 目标CPU开销 | 极低 | 中（中断驱动） |
| 可用性 | 需调试器 | 始终可用 |

---

## 6. 完整代码示例

### 6.1 完整调试配置

```rust
// Cargo.toml
[package]
name = "embedded-app"
version = "0.1.0"
edition = "2021"

[dependencies]
cortex-m = { version = "0.7", features = ["critical-section-single-core"] }
cortex-m-rt = "0.7"
embassy-executor = { version = "0.5", features = ["arch-cortex-m", "executor-thread"] }
embassy-time = { version = "0.3", features = ["tick-hz-32_768"] }
embassy-nrf = { version = "0.1", features = ["nrf52840", "time-driver-rtc1"] }

# 日志和调试
defmt = "0.3"
defmt-rtt = "0.4"
panic-probe = { version = "0.3", features = ["print-defmt"] }

# 配置文件
[features]
default = ["debug"]
debug = []
production = ["panic-reset"]

[profile.dev]
debug = 2
opt-level = 1

[profile.release]
debug = 2
opt-level = "z"
lto = true

// .cargo/config.toml
[target.'cfg(all(target_arch = "arm", target_os = "none"))']
runner = "probe-rs run --chip nRF52840_xxAA"

rustflags = [
    "-C", "link-arg=-Tlink.x",
    "-C", "link-arg=-Tdefmt.x",
]

[build]
target = "thumbv7em-none-eabihf"

// src/lib.rs
#![no_std]
#![no_main]

use defmt::*;
use embassy_executor::Spawner;
use embassy_time::{Duration, Timer};
use panic_probe as _;

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    info!("Hello World!");

    loop {
        info!("tick");
        Timer::after(Duration::from_secs(1)).await;
    }
}
```

### 6.2 自定义Panic处理器

```rust
// src/panic_handler.rs

use core::panic::PanicInfo;
use core::sync::atomic::{AtomicU32, Ordering};
use cortex_m::peripheral::SCB;
use defmt::error;

/// Panic统计
static PANIC_COUNT: AtomicU32 = AtomicU32::new(0);
static PANIC_TIMESTAMP: AtomicU64 = AtomicU64::new(0);

/// Panic处理器配置
pub struct PanicConfig {
    /// 最大允许panic次数
    pub max_panics: u32,
    /// 是否通过RTT输出
    pub enable_rtt: bool,
    /// 是否记录到闪存
    pub enable_flash_log: bool,
    /// 复位延迟（毫秒）
    pub reset_delay_ms: u32,
}

impl Default for PanicConfig {
    fn default() -> Self {
        Self {
            max_panics: 3,
            enable_rtt: true,
            enable_flash_log: cfg!(feature = "flash-log"),
            reset_delay_ms: 100,
        }
    }
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    // 禁用中断
    cortex_m::interrupt::disable();

    // 获取panic计数
    let count = PANIC_COUNT.fetch_add(1, Ordering::SeqCst);

    // 记录时间戳
    PANIC_TIMESTAMP.store(get_timestamp(), Ordering::SeqCst);

    // 输出panic信息
    report_panic(info, count);

    // 决定处理策略
    if count < 3 {
        // 前几次panic：复位重试
        perform_reset();
    } else {
        // 多次panic：进入安全模式
        enter_safe_mode();
    }
}

fn report_panic(info: &PanicInfo, count: u32) {
    error!("╔══════════════════════════════════════╗");
    error!("║           PANIC #{:<3}                ║", count);
    error!("╚══════════════════════════════════════╝");

    if let Some(location) = info.location() {
        error!("Location: {}:{}:{}",
            location.file(),
            location.line(),
            location.column()
        );
    }

    if let Some(message) = info.message() {
        error!("Message: {}", message);
    }

    // 捕获栈回溯
    capture_backtrace();

    // 输出系统状态
    report_system_state();
}

fn capture_backtrace() {
    error!("Stack backtrace:");

    // 获取当前LR和SP
    let lr: u32;
    let sp: u32;
    unsafe {
        asm!(
            "mov {0}, lr\n\tmov {1}, sp",
            out(reg) lr,
            out(reg) sp,
        );
    }

    error!("  LR: 0x{:08X}", lr);
    error!("  SP: 0x{:08X}", sp);

    // 遍历栈帧
    let mut frame = sp;
    let mut depth = 0;

    while frame != 0 && depth < 16 {
        unsafe {
            let pc = *(frame as *const u32).offset(6); // PC在异常帧中
            if pc != 0 && pc != 0xFFFFFFFF {
                error!("  #{}: PC=0x{:08X}", depth, pc);
            }
            frame = *(frame as *const u32); // 上一个帧指针
        }
        depth += 1;
    }
}

fn report_system_state() {
    // 输出寄存器状态
    let ipsr: u32;
    unsafe {
        asm!("mrs {0}, ipsr", out(reg) ipsr);
    }

    error!("IPSR: 0x{:08X} (Exception number: {})",
        ipsr, ipsr & 0x1FF);

    // 输出时钟状态
    // ...
}

fn perform_reset() {
    error!("Performing system reset...");

    // 短暂延迟（确保日志输出完成）
    for _ in 0..100000 {
        cortex_m::asm::nop();
    }

    // 系统复位
    SCB::sys_reset();
}

fn enter_safe_mode() {
    error!("Entering safe mode (too many panics)");

    // 关闭所有外设
    disable_peripherals();

    // 设置错误LED
    set_error_led();

    // 进入低功耗循环
    loop {
        cortex_m::asm::wfi();
    }
}

fn disable_peripherals() {
    // 实现取决于具体硬件
}

fn set_error_led() {
    // 实现取决于具体硬件
}

fn get_timestamp() -> u64 {
    // 使用SysTick或RTC
    0
}
```

### 6.3 故障日志系统

```rust
// src/fault_log.rs

use littlefs2::fs::{Filesystem, File, OpenOptions};
use littlefs2::io::Write;
use serde::{Serialize, Deserialize};

/// 故障记录
#[derive(Serialize, Deserialize, Debug)]
pub struct FaultRecord {
    pub timestamp: u64,
    pub fault_type: FaultType,
    pub location: FaultLocation,
    pub context: FaultContext,
    pub stack_hash: u32,
}

#[derive(Serialize, Deserialize, Debug, Clone, Copy)]
pub enum FaultType {
    Panic,
    AssertFailed,
    HardFault,
    BusFault,
    UsageFault,
    WatchdogTimeout,
    StackOverflow,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct FaultLocation {
    pub file: String<64>,
    pub line: u32,
    pub column: u32,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct FaultContext {
    pub task_id: u32,
    pub priority: u8,
    pub registers: [u32; 16],
}

/// 故障日志管理器
pub struct FaultLog<'a> {
    fs: &'a Filesystem<FlashStorage>,
}

impl<'a> FaultLog<'a> {
    pub fn new(fs: &'a Filesystem<FlashStorage>) -> Self {
        Self { fs }
    }

    /// 记录故障
    pub fn record_fault(&mut self, record: &FaultRecord) -> Result<(), Error> {
        // 序列化
        let data = postcard::to_vec::<_, 256>(record)
            .map_err(|_| Error::SerializationFailed)?;

        // 写入日志文件
        self.fs.open_file_with_options_and_then(
            |opt| opt.write(true).create(true).append(true),
            "/faults.bin",
            |file| {
                // 写入长度前缀
                let len = data.len() as u16;
                file.write_all(&len.to_le_bytes())?;
                // 写入数据
                file.write_all(&data)?;
                file.sync()?;
                Ok(())
            }
        )?;

        Ok(())
    }

    /// 读取所有故障记录
    pub fn read_faults<F>(&mut self, mut callback: F) -> Result<(), Error>
    where
        F: FnMut(&FaultRecord) -> Result<(), Error>
    {
        self.fs.open_file_with_options_and_then(
            |opt| opt.read(true),
            "/faults.bin",
            |file| {
                let mut len_buf = [0u8; 2];

                while file.read_exact(&mut len_buf).is_ok() {
                    let len = u16::from_le_bytes(len_buf) as usize;

                    let mut data = vec![0u8; len];
                    file.read_exact(&mut data)?;

                    let record: FaultRecord = postcard::from_bytes(&data)
                        .map_err(|_| Error::DeserializationFailed)?;

                    callback(&record)?;
                }

                Ok(())
            }
        )?;

        Ok(())
    }

    /// 清除故障日志
    pub fn clear(&mut self) -> Result<(), Error> {
        self.fs.remove("/faults.bin")?;
        Ok(())
    }

    /// 获取故障统计
    pub fn statistics(&mut self) -> Result<FaultStatistics, Error> {
        let mut stats = FaultStatistics::default();

        self.read_faults(|record| {
            stats.total += 1;
            match record.fault_type {
                FaultType::Panic => stats.panics += 1,
                FaultType::AssertFailed => stats.asserts += 1,
                FaultType::HardFault => stats.hard_faults += 1,
                _ => stats.others += 1,
            }
            Ok(())
        })?;

        Ok(stats)
    }
}

#[derive(Default)]
pub struct FaultStatistics {
    pub total: u32,
    pub panics: u32,
    pub asserts: u32,
    pub hard_faults: u32,
    pub others: u32,
}
```

### 6.4 多级恢复策略

```rust
// src/recovery.rs

use core::sync::atomic::{AtomicU8, Ordering};

/// 恢复级别
#[derive(Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum RecoveryLevel {
    /// 无需恢复
    None = 0,
    /// 任务级恢复：重启单个任务
    Task = 1,
    /// 子系统级恢复：重新初始化子系统
    Subsystem = 2,
    /// 系统级恢复：软复位
    System = 3,
    /// 硬件级恢复：硬复位
    Hardware = 4,
}

/// 恢复管理器
pub struct RecoveryManager {
    level: AtomicU8,
    attempt_count: AtomicU32,
    max_attempts: u32,
}

impl RecoveryManager {
    pub const fn new(max_attempts: u32) -> Self {
        Self {
            level: AtomicU8::new(RecoveryLevel::None as u8),
            attempt_count: AtomicU32::new(0),
            max_attempts,
        }
    }

    /// 处理故障并尝试恢复
    pub fn handle_fault(&self, fault: &FaultInfo) -> ! {
        let count = self.attempt_count.fetch_add(1, Ordering::SeqCst);

        if count >= self.max_attempts {
            // 超过最大尝试次数，进入安全状态
            self.enter_safe_state();
        }

        // 根据故障类型选择恢复级别
        let level = self.determine_recovery_level(fault);
        self.level.store(level as u8, Ordering::SeqCst);

        match level {
            RecoveryLevel::None => {
                // 继续执行
                self.continue_execution();
            }
            RecoveryLevel::Task => {
                self.recover_task(fault);
            }
            RecoveryLevel::Subsystem => {
                self.recover_subsystem(fault);
            }
            RecoveryLevel::System => {
                self.system_reset();
            }
            RecoveryLevel::Hardware => {
                self.hardware_reset();
            }
        }
    }

    fn determine_recovery_level(&self, fault: &FaultInfo) -> RecoveryLevel {
        use FaultType::*;

        match fault.fault_type {
            WatchdogTimeout => RecoveryLevel::Task,
            AssertFailed => RecoveryLevel::Subsystem,
            Panic => RecoveryLevel::System,
            HardFault | BusFault => RecoveryLevel::Hardware,
            _ => RecoveryLevel::System,
        }
    }

    fn recover_task(&self, fault: &FaultInfo) {
        defmt::warn!("Recovering task {:?}", fault.task_id);

        // 停止故障任务
        stop_task(fault.task_id);

        // 清理任务资源
        cleanup_task_resources(fault.task_id);

        // 重启任务
        restart_task(fault.task_id);

        // 恢复执行
        self.continue_execution();
    }

    fn recover_subsystem(&self, fault: &FaultInfo) {
        defmt::warn!("Recovering subsystem");

        // 进入降级模式
        enter_degraded_mode();

        // 重新初始化子系统
        reinitialize_subsystems();

        // 验证恢复
        if verify_subsystems() {
            self.continue_execution();
        } else {
            // 子系统恢复失败，升级恢复级别
            self.system_reset();
        }
    }

    fn system_reset(&self) {
        defmt::error!("Performing system reset");

        // 保存关键状态
        save_critical_state();

        // 延迟确保日志输出
        delay_ms(100);

        // 软复位
        cortex_m::peripheral::SCB::sys_reset();
    }

    fn hardware_reset(&self) {
        defmt::error!("Performing hardware reset");

        // 触发外部看门狗
        trigger_external_watchdog();

        // 如果看门狗失败，进入无限循环
        loop {
            cortex_m::asm::wfi();
        }
    }

    fn enter_safe_state(&self) -> ! {
        defmt::error!("Entering safe state");

        // 关闭所有输出
        disable_all_outputs();

        // 设置安全状态标志
        set_safe_state_flag();

        // 通知外部
        notify_external_monitor();

        // 无限循环
        loop {
            blink_error_led();
            delay_ms(500);
        }
    }

    fn continue_execution(&self) -> ! {
        // 从panic处理器返回（通过长跳转）
        unsafe {
            // 恢复上下文并返回
            restore_context_and_return();
        }
    }
}

// 辅助函数（占位）
fn stop_task(_task_id: u32) {}
fn cleanup_task_resources(_task_id: u32) {}
fn restart_task(_task_id: u32) {}
fn enter_degraded_mode() {}
fn reinitialize_subsystems() {}
fn verify_subsystems() -> bool { true }
fn save_critical_state() {}
fn delay_ms(_ms: u32) {}
fn trigger_external_watchdog() {}
fn disable_all_outputs() {}
fn set_safe_state_flag() {}
fn notify_external_monitor() {}
fn blink_error_led() {}
fn restore_context_and_return() -> ! { loop {} }
```

---

## 7. 性能分析

### 7.1 Panic处理延迟

```rust
// 测量panic处理时间
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    let start = DWT::get_cycle_count();

    // panic处理
    report_panic(info);

    let end = DWT::get_cycle_count();
    let cycles = end - start;
    let microseconds = cycles / 64; // 假设64MHz

    // 输出处理时间
    // ...
}

// 典型延迟（Cortex-M4 @ 64MHz）:
// - 简单halt: ~10 cycles (0.16 µs)
// - RTT输出: ~1000 cycles (15 µs)
// - 完整栈回溯: ~10000 cycles (156 µs)
```

### 7.2 代码大小开销

| 处理器 | 代码大小 | 数据大小 |
|-------|---------|---------|
| panic-halt | ~50B | 0B |
| panic-reset | ~100B | 0B |
| panic-probe | ~1KB | ~100B |
| panic-semihosting | ~2KB | ~200B |
| 自定义（完整功能） | ~3KB | ~500B |

### 7.3 运行时开销

正常运行时开销（无panic）：

- 代码占用：Flash中
- 运行时：零开销（panic处理器不执行）

Panic发生时开销：

- 中断禁用：立即停止任务调度
- 信息收集：取决于配置
- 输出传输：取决于通道带宽

---

## 8. 最佳实践

### 8.1 Panic处理器选择

```rust
// 开发阶段：最大调试信息
#[cfg(debug_assertions)]
mod panic_config {
    use panic_probe as _;
}

// 发布阶段：自动恢复
#[cfg(not(debug_assertions)))]
mod panic_config {
    #[panic_handler]
    fn panic(_info: &PanicInfo) -> ! {
        cortex_m::peripheral::SCB::sys_reset();
    }
}
```

### 8.2 调试信息配置

```toml
# Cargo.toml
[profile.dev]
debug = 2          # 完整调试信息
opt-level = 1      # 轻微优化，保持调试能力

[profile.release]
debug = 2          # 保留调试信息
opt-level = "z"    # 大小优化
lto = true         # 链接时优化
```

### 8.3 故障恢复模式

```rust
// 恢复状态机
enum RecoveryState {
    Normal,
    Degraded,
    RecoveryInProgress,
    Failed,
}

impl RecoveryState {
    fn transition(&mut self, event: RecoveryEvent) {
        *self = match (*self, event) {
            (Normal, FaultDetected) => {
                start_recovery();
                RecoveryInProgress
            }
            (RecoveryInProgress, RecoverySuccess) => Normal,
            (RecoveryInProgress, RecoveryFailed) => {
                if attempt_count < MAX_ATTEMPTS {
                    start_recovery();
                    RecoveryInProgress
                } else {
                    Failed
                }
            }
            (Failed, ManualReset) => Normal,
            _ => *self, // 无变化
        };
    }
}
```

### 8.4 安全考虑

```rust
// 安全关键系统的panic处理
#[cfg(feature = "safety-critical")]
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    // 1. 立即进入安全状态（不改变输出）
    enter_safe_state();

    // 2. 记录故障（如果可能）
    let _ = log_to_nvram(info);

    // 3. 通知外部监控
    signal_external_watchdog();

    // 4. 等待外部处理
    loop {
        cortex_m::asm::wfi();
    }
}
```

---

## 9. 形式化定理与证明

### 9.1 Panic不返回定理

**定理 9.1** (Panic Handler Divergence)

> Rust panic处理器永不返回正常控制流。

**形式化表述**：

$$
\forall h: \text{PanicHandler}.\ h: \text{PanicInfo} \to \bot
$$

其中 $\bot$ 表示发散（divergence）。

**证明**：

由Rust语言规范，panic处理器签名必须返回 `!` 类型。

`!` 类型（never type）无任何值，因此：

1. 无返回值的函数体必须以发散表达式结束
2. 常见的分歧构造：`loop {}`、`panic!()`、`exit()`、`reset()`
3. 编译器验证所有控制路径都以发散结束

因此，任何合法的panic处理器实现都永不返回。∎

### 9.2 探针非侵入性定理

**定理 9.2** (Probe Non-Intrusiveness)

> RTT/panic-probe在正常执行时不影响目标程序行为。

**证明**：

RTT机制：

1. 缓冲区在内存中，写入为简单内存操作
2. 调试探针通过SWD/JTAG独立读取
3. 无中断、无目标CPU开销
4. 仅当缓冲区满时可能阻塞（可配置为丢弃）

形式化：

设 $P$ 为程序执行轨迹，$P'$ 为连接探针时的执行轨迹。

$$
\forall t: \text{observable}(P_t) = \text{observable}(P'_t)
$$

除了日志输出外，程序可观察行为一致。∎

### 9.3 栈回溯完整性定理

**定理 9.3** (Stack Trace Completeness)

> 在启用完整调试信息时，栈回溯包含所有调用帧。

**证明**：

ARM Cortex-M的异常/调用约定：

1. 函数调用时，LR保存返回地址
2. 函数序言保存帧指针（如果启用）
3. 回溯算法跟随帧指针链

完整性条件：

- 所有函数有标准序言 → 帧指针有效
- 未优化代码或 `-fno-omit-frame-pointer`
- 无内联汇编破坏帧指针

在以上条件下，回溯算法可以访问完整的调用链。∎

---

## 10. 反例与边界情况

### 10.1 堆栈溢出

```rust
// 问题：栈溢出可能导致双重panic
fn recursive_function(depth: usize) {
    let large_array = [0u8; 1024];
    if depth > 0 {
        recursive_function(depth - 1);
    }
    // 使用数组防止优化
    core::hint::black_box(large_array);
}

// 当栈溢出时：
// 1. 触发HardFault
// 2. HardFault处理中可能再次发生异常
// 3. 导致双重panic

// 解决方案：栈溢出检查
#[no_mangle]
unsafe extern "C" fn HardFault(_frame: &ExceptionFrame) -> ! {
    // 检查是否来自栈溢出
    if _frame.psr & 0x1FF == 0 {
        // 记录并停止
        defmt::error!("Stack overflow detected!");
        loop {}
    }
    // 正常处理
}
```

### 10.2 双重Panic

```rust
// 问题：panic处理中再次panic
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    defmt::error!("PANIC: {}", info);  // 如果这里panic...
    loop {}
}

// 如果defmt输出失败（如RTT缓冲区无效）
// 会导致双重panic

// 解决方案：防御性编程
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    // 使用原始输出，不依赖可能失败的组件
    unsafe {
        let uart = UART0::ptr();
        write_str_raw(uart, b"PANIC\n");
    }
    loop {}
}
```

### 10.3 硬件故障

```rust
// 问题：硬件故障可能破坏panic处理
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    // 如果Flash损坏，这里可能无效指令
    // 如果RAM损坏，栈可能不可用
    loop {}
}

// 解决方案：多层级保护
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    // 第1层：尝试RTT输出
    if rtt_is_valid() {
        rtt_output("PANIC");
    }

    // 第2层：尝试UART
    if uart_is_available() {
        uart_output("PANIC");
    }

    // 第3层：设置GPIO指示
    set_panic_led();

    // 第4层：看门狗复位
    trigger_watchdog();

    // 最终防线
    loop {}
}
```

---

**文档版本**: 2.0.0
**最后更新**: 2026-03-10
**状态**: ✅ 深度技术分析
**定理数量**: 3个
**代码示例**: 6个完整示例
