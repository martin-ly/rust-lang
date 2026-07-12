# Embedded-HAL 1.0 迁移与 Embassy 生产状态

> **EN**: Embedded-HAL 1.0 Migration and Embassy Production Status
> **Summary**: Key breaking changes and migration strategies from `embedded-hal` 0.2 to 1.0, including the unified `ErrorType`, `SpiDevice` versus `SpiBus` separation, async trait support, and the production-ready status of Embassy v0.5 in embedded Rust.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **权威来源**: [embedded-hal 1.0.0](https://github.com/rust-embedded/embedded-hal/releases/tag/embedded-hal-v1.0.0) · [Embassy 文档](https://embassy.dev/) · [Rust Embedded Working Group](https://github.com/rust-embedded/wg)
>
> **受众**: [进阶 / 工程]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **A+S** — Application + Structure
> **前置概念**: [Rust 嵌入式系统开发](03_embedded_systems.md) · [Traits](../../02_intermediate/00_traits/01_traits.md)
> **后置概念**: [交叉编译](02_cross_compilation.md)

---

> **文档状态**: ✅ 完成
> **更新日期**: 2026-06-01
> **对标版本**: embedded-hal 1.0.0 / embedded-hal-async 1.0.0 / Embassy v0.5
> **难度等级**: ⭐⭐⭐⭐

---

## 一、Embedded-HAL 生态现状（2026-06）

「Embedded-HAL 生态现状（2026-06）」部分包含版本里程碑 与 为什么 1.0 是重大变革 两条主线，本节依次说明。

### 1.1 版本里程碑

| Crate | 旧版本 | 当前稳定版本 | 状态 |
| :--- | :--- | :--- | :--- |
| `embedded-hal` | 0.2.7 | **1.0.0** (2024-01) | ✅ 稳定 |
| `embedded-hal-async` | 0.2.x | **1.0.0** (2024-01) | ✅ 稳定 |
| `embedded-hal-nb` | 0.1.x | 1.0.0 | ✅ 稳定 |
| `embassy` | 0.2.x | **0.5.x** (2026) | ✅ 生产就绪 |

### 1.2 为什么 1.0 是重大变革

`embedded-hal` 1.0 解决了 0.2 时代的核心设计缺陷：

```text
embedded-hal 0.2 的问题:
├── SPI/I2C/UART trait 使用关联类型定义错误类型 → 难以组合
├── 阻塞 API 与异步 API 分离在不同 crate → 生态碎片化
├── 缺乏标准方式表达 "可重入性" 和 "互斥"
└── GPIO 状态机表达不完整

embedded-hal 1.0 的解决:
├── 统一错误类型: ErrorType trait + 标准错误码
├── 内置异步支持: embedded-hal-async 与阻塞 API 平行设计
├── 显式所有权: SpiDevice / SpiBus 分离
└── GPIO 完整状态机: Input/Output/OpenDrain 显式类型
```

---

## 二、Embedded-HAL 1.0 核心变化

本节将「Embedded-HAL 1.0 核心变化」分解为若干主题：错误类型统一、SpiDevice vs SpiBus 分离与异步 HAL (embedded-hal-async)。

### 2.1 错误类型统一

**0.2 写法（碎片化）**:

```rust
// 每个 HAL 实现自己的错误类型
pub enum MySpiError { Timeout, BusBusy, CsFault }
impl spi::Write<u8> for MySpi { type Error = MySpiError; }
// 不同 HAL 的错误类型不兼容，上层库难以通用
```

**1.0 写法（统一）**:

```rust
use embedded_hal::spi::{ErrorType, ErrorKind, SpiDevice};

impl ErrorType for MySpi {
    type Error = ErrorKind; // 标准错误码: NoDevice, Crc, Overrun...
}

impl SpiDevice<u8> for MySpi {
    fn transaction(&mut self, operations: &mut [Operation<'_, u8>])
        -> Result<(), Self::Error> { ... }
}
```

### 2.2 SpiDevice vs SpiBus 分离

1.0 明确区分两种 SPI 使用模式：

| 类型 | 所有权（Ownership） | CS 管理 | 适用场景 |
|:---|:---|:---|:---|
| `SpiBus` | 独占总线 | 手动控制 CS | 单一设备、高性能 |
| `SpiDevice` | 共享总线 | 自动 CS 管理 | 多设备、安全易用 |

```rust
use embedded_hal::spi::{SpiBus, SpiDevice};

// SpiBus: 独占使用，手动控制片选
fn raw_transfer(bus: &mut impl SpiBus<u8>, cs: &mut impl OutputPin) {
    cs.set_low().unwrap();
    bus.transfer(&mut [0x01, 0x00]).unwrap();
    cs.set_high().unwrap();
}

// SpiDevice: 共享使用，CS 自动管理
fn device_transfer(dev: &mut impl SpiDevice<u8>) {
    dev.transaction(&mut [
        Operation::TransferInPlace(&mut [0x01, 0x00]),
    ]).unwrap();
}
```

### 2.3 异步 HAL (embedded-hal-async)

```rust
use embedded_hal_async::spi::SpiDevice;
use embedded_hal_async::digital::Wait; // 等待 GPIO 边沿的异步 trait

async fn read_sensor(spi: &mut impl SpiDevice<u8>, drdy: &mut impl Wait) {
    drdy.wait_for_high().await.unwrap(); // 异步等待数据就绪
    let mut buf = [0u8; 4];
    spi.read(&mut buf).await.unwrap();
}
```

---

## 三、Embassy v0.5 生产就绪状态

本节围绕「Embassy v0.5 生产就绪状态」展开，依次讨论 Embassy 是什么、v0.5 关键特性与Embassy vs RTIC 选型。

### 3.1 Embassy 是什么

Embassy 是 Rust 嵌入式生态的 **async/await 运行时（Runtime）**，允许在裸机（bare-metal）环境中使用异步编程模型。

### 3.2 v0.5 关键特性

| 特性 | 说明 | 状态 |
|:---|:---|:---:|
| **Stable Rust 支持** | Embassy MSRV 1.75，无需每日构建版工具链 | ✅ |
| **Time Driver** | 硬件定时器驱动异步（Async） Timer/Ticker | ✅ |
| **USB 协议栈** | 全栈 async USB device/host | ✅ |
| **TCP/UDP 网络** | async smoltcp 集成 | ✅ |
| **WiFi/BLE** | CYW43、nrf-softdevice 绑定 | ✅ |
| **LORA** | 异步（Async） LoRa 驱动 | ✅ |
| **多核支持** | RP2040 双核、ESP32 等 | 🧪 实验 |

### 3.3 Embassy vs RTIC 选型

| 维度 | Embassy | RTIC |
|:---|:---|:---|
| 编程模型 | async/await | 基于硬件任务的优先级调度 |
| 内存分配 | 共享调用栈（推荐静态） | 每个任务独立栈 |
| 实时性 | 协作式（cooperative） | 硬实时（优先级抢占） |
| 学习曲线 | 低（熟悉 Tokio 即可） | 中（需理解优先级模型） |
| 适用场景 | 复杂协议栈、网络设备 | 硬实时控制、 motor control |
| 生态成熟度 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |

---

## 四、从 0.2 迁移到 1.0 的行动指南

「从 0.2 迁移到 1.0 的行动指南」部分按 Cargo.toml 更新、代码迁移要点与迁移检查清单的顺序逐层展开。

### 4.1 Cargo.toml 更新

```toml
# 旧依赖 (embedded-hal 0.2)
# embedded-hal = "0.2.7"

# 新依赖 (embedded-hal 1.0)
[dependencies]
embedded-hal = "1.0"
embedded-hal-async = "1.0"  # 如需异步支持

# Embassy 生态
embassy-executor = { version = "0.5", features = ["task-arena-size-32768"] }
embassy-time = "0.5"
embassy-stm32 = { version = "0.5", features = ["stm32g474re"] }
```

### 4.2 代码迁移要点

```rust
// ========== 0.2 API ==========
use embedded_hal::blocking::spi::{Write, Transfer};
use embedded_hal::digital::v2::OutputPin;

impl Write<u8> for MySpi {
    type Error = MyError;
    fn write(&mut self, words: &[u8]) -> Result<(), Self::Error> { ... }
}

// ========== 1.0 API ==========
use embedded_hal::spi::{ErrorType, SpiDevice};
use embedded_hal::digital::OutputPin;

impl ErrorType for MySpi {
    type Error = embedded_hal::spi::ErrorKind;
}

impl SpiDevice<u8> for MySpi {
    fn transaction(&mut self, ops: &mut [Operation<'_, u8>])
        -> Result<(), Self::Error> { ... }
}
```

### 4.3 迁移检查清单

- [ ] 更新 `Cargo.toml`: `embedded-hal = "1.0"`
- [ ] 将 `blocking::spi::Write`/`Transfer` 替换为 `spi::SpiDevice`
- [ ] 将自定义错误类型替换为 `ErrorKind` 或实现 `ErrorType`
- [ ] 更新 GPIO 代码: `v2::OutputPin` → `digital::OutputPin`
- [ ] 如需异步: 添加 `embedded-hal-async` 依赖
- [ ] 测试所有外设驱动（SPI/I2C/UART/GPIO）

---

## 五、来源与参考

| 来源 | 说明 |
|:---|:---|
| [embedded-hal 1.0.0 Docs](https://docs.rs/embedded-hal/1.0.0) | 官方 API 文档 |
| [Embassy Book](https://embassy.dev/book/) | Embassy 官方文档 |
| [embedded-hal Migration Guide](https://github.com/rust-embedded/embedded-hal/blob/master/docs/migrating-from-0.2-to-1.0.md) | 官方迁移指南 |
| [Rust Embedded WG](https://github.com/rust-embedded/wg) | 嵌入式工作组 |

> **L5 对比**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)

## 过渡段

> **过渡**: 从 embedded-hal 0.2 的 trait 模型过渡到 1.0 的统一错误类型，可以理解生态标准化的方向。
>
> **过渡**: 从 trait 签名变化过渡到驱动代码更新，可以建立版本迁移的影响范围评估方法。
>
> **过渡**: 从代码更新过渡到 CI 与硬件验证，可以确保迁移后的行为一致性（Coherence）。
>

## 定理链

| 定理 | 前提 | 结论 |
|:---|:---|:---|
| 稳定 HAL API ⟹ 生态可移植性 | 统一硬件抽象接口 | 驱动与板级支持代码复用性提升 |
| 类型级错误 ⟹ 编译期检查 | 1.0 引入的错误关联类型 | 更多问题在编译期暴露 |
| 验证矩阵 ⟹ 硬件覆盖 | 在目标硬件上运行测试 | 降低迁移回归风险 |

---

## 国际权威参考 / International Authority References（P0 官方 · P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P0 官方**: [core — Rust 核心库（no_std 官方 API 文档）](https://doc.rust-lang.org/core/index.html)
- **P1 学术/形式化**: [Sharma, Sharma, Torres-Arias & Machiry: Rust for Embedded Systems — Current State, Challenges and Open Problems（CCS 2024 扩展报告, arXiv:2311.05063）](https://arxiv.org/abs/2311.05063)（2026-07-12 验证 HTTP 200）
