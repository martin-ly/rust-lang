# Panic-Probe与嵌入式Panic处理形式化分析

> **主题**: 嵌入式Panic处理与调试
> **形式化框架**: 错误恢复 + 调试输出
> **参考**: knurling-rs tools (<https://knurling.ferrous-systems.com>)

---

## 目录

- [Panic-Probe与嵌入式Panic处理形式化分析](#panic-probe与嵌入式panic处理形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. Panic模型形式化](#2-panic模型形式化)
    - [定义 PANIC-1 ( Panic状态 )](#定义-panic-1--panic状态-)
    - [定义 PANIC-2 ( Panic处理器类型 )](#定义-panic-2--panic处理器类型-)
    - [定义 PANIC-3 ( Panic处理器语义 )](#定义-panic-3--panic处理器语义-)
  - [3. Panic处理策略](#3-panic处理策略)
    - [定理 PANIC-T1 ( Panic不返回 )](#定理-panic-t1--panic不返回-)
    - [定义 RECOVERY-1 ( 复位恢复 )](#定义-recovery-1--复位恢复-)
  - [4. Defmt日志形式化](#4-defmt日志形式化)
    - [定义 DEFMT-1 ( 压缩日志 )](#定义-defmt-1--压缩日志-)
    - [定义 DEFMT-2 ( 日志级别 )](#定义-defmt-2--日志级别-)
    - [定理 DEFMT-T1 ( 零开销过滤 )](#定理-defmt-t1--零开销过滤-)
  - [5. 定理与证明](#5-定理与证明)
    - [定理 SAFE-T1 ( Probe-rs安全 )](#定理-safe-t1--probe-rs安全-)
    - [定理 DEBUG-T1 ( 栈回溯完整性 )](#定理-debug-t1--栈回溯完整性-)
  - [6. 代码示例](#6-代码示例)
    - [示例1: Panic Probe配置](#示例1-panic-probe配置)
    - [示例2: 自定义Panic处理](#示例2-自定义panic处理)
    - [示例3: Defmt日志使用](#示例3-defmt日志使用)
    - [示例4: 运行时日志级别](#示例4-运行时日志级别)

---

## 1. 引言

嵌入式系统中，panic处理至关重要：

- **panic-probe**: 通过调试探针输出panic信息
- **panic-halt**: 进入无限循环
- **panic-reset**: 系统复位
- **defmt**: 压缩日志输出

---

## 2. Panic模型形式化

### 定义 PANIC-1 ( Panic状态 )

$$
\text{Panic} = \{
    \text{info} : \text{PanicInfo},
    \text{location} : \text{Location},
    \text{message} : \text{Option}<\&str>
\}
$$

### 定义 PANIC-2 ( Panic处理器类型 )

| 处理器 | 行为 | 用途 |
| :--- | :--- | :--- |
| `panic-halt` | `loop {}` | 生产环境 |
| `panic-reset` | 系统复位 | 自动恢复 |
| `panic-probe` | 通过RTT输出 | 调试 |
| `panic-semihosting` | 通过semihosting输出 | 仿真 |

### 定义 PANIC-3 ( Panic处理器语义 )

$$
\text{panic\_handler}(\text{info}) : \text{PanicInfo} \to \bot
$$

其中$\bot$表示发散（永不返回）。

---

## 3. Panic处理策略

### 定理 PANIC-T1 ( Panic不返回 )

所有panic处理器必须发散。

$$
\forall h : \text{PanicHandler}.\ h : \text{PanicInfo} \to \bot
$$

**证明**: 由Rust语言规范，panic后程序状态不可恢复，不能返回正常控制流。$\square$

### 定义 RECOVERY-1 ( 复位恢复 )

```rust
#[inline(never)]
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    cortex_m::peripheral::SCB::sys_reset();
}
```

**形式化**:

$$
\text{panic} \to \text{sys\_reset} \to \text{program\_restart}
$$

---

## 4. Defmt日志形式化

### 定义 DEFMT-1 ( 压缩日志 )

```rust
defmt::info!("Value: {}", value);
```

**形式化**:

$$
\text{defmt\_log}(\text{template}, \text{args}) = \text{send}(\text{template\_id}, \text{encoded\_args})
$$

**压缩比**:

$$
\frac{|\text{defmt\_output}|}{|\text{format!|}} \approx \frac{1}{10}
$$

### 定义 DEFMT-2 ( 日志级别 )

$$
\text{LogLevel} = \{ \text{Trace}, \text{Debug}, \text{Info}, \text{Warn}, \text{Error} \}
$$

**过滤**:

$$
\text{log}(level, msg) = \begin{cases}
\text{output}(msg) & \text{if } level \geq \text{filter} \\
\text{nop} & \text{otherwise}
\end{cases}
$$

### 定理 DEFMT-T1 ( 零开销过滤 )

编译时日志级别过滤无运行时开销。

$$
\text{DEFMT\_LOG} = \text{\"off\"} \rightarrow \text{log\_calls} \equiv \text{nop}
$$

**证明**: 由编译器优化，被禁用的日志调用在编译时被移除。$\square$

---

## 5. 定理与证明

### 定理 SAFE-T1 ( Probe-rs安全 )

probe-rs调试不会干扰程序执行。

$$
\text{probe-rs} \vdash \text{non-intrusive} \lor \text{atomic-halt}
$$

### 定理 DEBUG-T1 ( 栈回溯完整性 )

启用debuginfo时，panic可输出完整栈回溯。

$$
\text{debuginfo} \land \text{panic-probe} \to \text{full\_stacktrace}
$$

---

## 6. 代码示例

### 示例1: Panic Probe配置

```rust
// Cargo.toml
[dependencies]
panic-probe = { version = "0.3", features = ["print-defmt"] }
defmt = "0.3"
defmt-rtt = "0.4"

// src/lib.rs
#![no_std]

use panic_probe as _;

#[defmt::panic_handler]
fn panic() -> ! {
    cortex_m::asm::udf();  // 触发硬fault便于调试
}
```

### 示例2: 自定义Panic处理

```rust
use core::panic::PanicInfo;
use cortex_m::peripheral::SCB;

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    // 记录panic信息到持久存储
    unsafe {
        let log = PANIC_LOG.as_mut_ptr();
        log.write(PanicRecord {
            message: info.message(),
            location: info.location(),
        });
    }

    // 尝试安全状态
    enter_safe_state();

    // 延时后复位
    for _ in 0..1_000_000 {
        cortex_m::asm::nop();
    }

    SCB::sys_reset();
}
```

### 示例3: Defmt日志使用

```rust
use defmt::*;

#[entry]
fn main() -> ! {
    info!("Starting application");

    let sensor_value = read_sensor();
    debug!("Raw sensor: {}", sensor_value);

    if let Ok(processed) = process(sensor_value) {
        info!("Processed: {}", processed);
    } else {
        error!("Processing failed!");
        panic!();
    }

    loop {
        tick();
        Timer::after(Duration::from_millis(100)).await;
    }
}
```

### 示例4: 运行时日志级别

```rust
#[derive(Debug, Clone, Copy)]
enum LogLevel {
    Error = 0,
    Warn = 1,
    Info = 2,
    Debug = 3,
    Trace = 4,
}

static LOG_LEVEL: AtomicU8 = AtomicU8::new(LogLevel::Info as u8);

fn set_log_level(level: LogLevel) {
    LOG_LEVEL.store(level as u8, Ordering::Relaxed);
}

macro_rules! log {
    ($level:expr, $fmt:literal $(, $arg:expr)*) => {
        if $level as u8 <= LOG_LEVEL.load(Ordering::Relaxed) {
            defmt::info!($fmt $(, $arg)*);
        }
    };
}
```

---

**维护者**: Rust Embedded Formal Methods Team
**创建日期**: 2026-03-05
**状态**: ✅ 已对齐
