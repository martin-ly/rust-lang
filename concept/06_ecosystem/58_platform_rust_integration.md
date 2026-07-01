# 将 Rust 集成到现有平台

> **内容分级**: [专家级]
>
> **代码状态**: [综述级 — 待补充可编译示例]
>
> **EN**: Integrating Rust into Existing Platforms and Codebases
> **Summary**: Integrating Rust into large platforms: Android, Chromium, Linux, and bare-metal firmware.
> **受众**: [专家]
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **A+S+P** — Application + Structure + Procedure
> **双维定位**: C×Eva — 评价 Rust 在不同平台约束下的工程实践
> **定位**: 系统对比 Android AOSP、Chromium、Bare Metal 三个典型场景中 Rust 的集成方式、构建系统、互操作模式与常见陷阱。
> **前置概念**: [Cross Compilation](17_cross_compilation.md) · [Embedded Systems](22_embedded_systems.md) · [Unsafe Rust](../03_advanced/03_unsafe.md) · [FFI](../03_advanced/05_rust_ffi.md) · [安全边界](../05_comparative/04_safety_boundaries.md)
> **后置概念**: [Industrial Case Studies](48_industrial_case_studies.md) · [OS Kernel](39_os_kernel.md)
> **来源**:
>
> [Android Rust](https://security.googleblog.com/2021/05/integrating-rust-into-android-open.html) ·
> [Chromium Rust](https://www.chromium.org/chromium-os/developer-library/guides/rust/rust-on-cros/) ·
> [Rust for Linux](https://rust-for-linux.com/)
> [Google Comprehensive Rust — Chromium](https://google.github.io/comprehensive-rust/chromium.html) ·
> [Google Comprehensive Rust — Bare Metal](https://google.github.io/comprehensive-rust/bare-metal.html) ·
> [AOSP Rust](https://security.googleblog.com/2021/05/integrating-rust-into-android-open.html) ·
> [Chromium Rust](https://chromium.googlesource.com/chromium/src/+/main/docs/rust.md) ·
> [The Embedded Rust Book](https://docs.rust-embedded.org/book/)
>
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链

---

## 📑 目录

- [将 Rust 集成到现有平台](#将-rust-集成到现有平台)
  - [📑 目录](#-目录)
  - [一、三种平台约束对比](#一三种平台约束对比)
  - [二、Android AOSP](#二android-aosp)
    - [2.1 AOSP 为什么选择 Rust](#21-aosp-为什么选择-rust)
    - [2.2 构建规则：Android.bp](#22-构建规则androidbp)
    - [2.3 AIDL 与 Binder IPC](#23-aidl-与-binder-ipc)
    - [2.4 C / C++ / Java 互操作](#24-c--c--java-互操作)
  - [三、Chromium](#三chromium)
    - [3.1 Chromium 的 Rust 策略](#31-chromium-的-rust-策略)
    - [3.2 GN 构建与 CXX](#32-gn-构建与-cxx)
    - [3.3 引入第三方 crate](#33-引入第三方-crate)
  - [四、Bare Metal](#四bare-metal)
    - [4.1 no\_std 与 alloc](#41-no_std-与-alloc)
    - [4.2 微控制器：PAC → HAL → Board Support](#42-微控制器pac--hal--board-support)
    - [4.3 应用处理器与 UART 驱动](#43-应用处理器与-uart-驱动)
  - [五、选型决策树](#五选型决策树)
  - [六、常见陷阱](#六常见陷阱)
  - [七、来源与延伸阅读](#七来源与延伸阅读)

---

## 一、三种平台约束对比

| 维度 | Android AOSP | Chromium | Bare Metal |
|:---|:---|:---|:---|
| **运行时（Runtime）环境** | 完整 OS，有 libc / Binder / JVM | 完整 OS（多平台），沙箱进程 | 无 OS 或极简 RTOS |
| **标准库** | `std` 可用 | `std` 可用 | `no_std`，可能无 `alloc` |
| **构建系统** | `Android.bp` (Soong) | `GN` + `ninja` | `cargo` + 链接脚本 / 厂商 SDK |
| **包管理** | `external/rust/crates/` 预审计 | `third_party/rust/` + `gnrt` | crates.io / 厂商 PAC/HAL |
| **主要互操作** | C / C++ / Java (JNI/AIDL) | C++ (CXX) | C / 汇编 / MMIO |
| **典型目标** | `aarch64-linux-android` | 宿主目标（多平台） | `thumbv7em-none-eabihf` / 自定义目标 |
| **安全驱动** | 消除内存漏洞（Binder、DNS、加密） | 沙箱边界安全、PDF/字体解析 | 资源受限下的安全关键固件 |

> **核心洞察**：三种场景共同点是 **Rust 都不拥有整个构建系统**，必须嵌入现有 C/C++ 主导的代码库。因此，互操作（FFI）与构建系统集成是学习的关键，而非 Rust 语法本身。

---

## 二、Android AOSP

### 2.1 AOSP 为什么选择 Rust

AOSP 是全球最大的开源代码库之一，数十亿设备运行。Rust 被引入主要为了：

1. **消除内存安全（Memory Safety）漏洞**：Binder、DNS 解析、加密库等系统组件历史上大量 bug 源于 C/C++ 的内存错误。
2. **与现有代码共存**：不替换整个子系统，而是对新组件或安全关键组件使用 Rust。
3. **利用类型系统（Type System）**：将运行时（Runtime）错误（如权限、生命周期（Lifetimes））前移到编译期。

> [来源: [Android Security Blog — Memory Safety in Android 14](https://security.googleblog.com/)] · 可信度: ✅

### 2.2 构建规则：Android.bp

AOSP 不使用 `Cargo.toml`，而是使用 Soong 构建系统的 `Android.bp`：

```bp
rust_binary {
    name: "my_rust_service",
    srcs: ["src/main.rs"],
    crate_name: "my_rust_service",
    edition: "2024",
    rustlibs: [
        "liblog_rust",
        "libbinder_rs",
    ],
}
```
关键点：

- `rust_binary` / `rust_library` / `rust_proc_macro` / `rust_test` 等模块（Module）类型
- `rustlibs` 依赖预置在 AOSP 中的 Rust crate（通常位于 `external/rust/crates/`）
- 所有依赖 crate 必须经过 AOSP 的审计与版本锁定

### 2.3 AIDL 与 Binder IPC

AOSP 中服务间通信大量使用 Binder。Rust 侧可通过 AIDL 生成绑定：

```rust,ignore
// AIDL 接口生成的 Rust 绑定
use binder::Interface;

pub trait IMyService: Interface {
    fn add(&self, a: i32, b: i32) -> binder::Result<i32>;
}
```
> **边界**：Rust AIDL 绑定目前覆盖常用类型，但复杂 Parcelable / 文件描述符传递需要额外注意生命周期（Lifetimes）与所有权（Ownership）。

### 2.4 C / C++ / Java 互操作

| 对端 | Rust 机制 | 说明 |
|:---|:---|:---|
| C / C++ | `unsafe extern "C"` / `bindgen` / `cxx` | 与 C++ 优先使用 `cxx` 生成类型安全桥接 |
| Java | JNI (via `jni` crate) | Rust 实现 native 方法，供 Java/Kotlin 调用 |
| AIDL | `libbinder_rs` | 生成 Binder 服务/客户端 |

---

## 三、Chromium

### 3.1 Chromium 的 Rust 策略

Chromium 对 Rust 的采用相对谨慎，核心原则：

1. **沙箱边界优先**：Rust 用于处理不可信输入的组件（如解析器），利用内存安全（Memory Safety）减少沙箱逃逸风险。
2. **与 C++ 深度互操作**：由于 Chromium 主体是 C++，Rust 必须无缝集成到 GN 构建系统。
3. **逐步引入**：从安全关键的小模块（Module）开始，而非重写核心引擎。

### 3.2 GN 构建与 CXX

Chromium 使用 `GN` 定义构建规则。Rust crate 通过 `rust_static_library` 或 `rust_shared_library` 引入：

```gn
rust_static_library("my_rust_parser") {
  crate_root = "src/lib.rs"
  sources = [ "src/lib.rs" ]
  edition = "2024"
  deps = [ "//third_party/rust/cxx/v1:cxx" ]
}
```
`cxx` crate 是 Chromium Rust↔C++ 互操作的核心：

```rust
// Rust 侧桥接模块
#[cxx::bridge]
mod ffi {
    unsafe extern "C++" {
        include!("my_parser_bridge.h");
        type ParserState;
        fn create_parser() -> UniquePtr<ParserState>;
        fn parse(state: Pin<&mut ParserState>, input: &str) -> bool;
    }
}
```
> **认知要点**：`cxx` 在编译期检查类型兼容性，避免手动 FFI 中常见的 ABI 错误。它是 Chromium 将 Rust 集成到 C++ 代码库的首选方案。

### 3.3 引入第三方 crate

Chromium 对第三方 crate 有严格流程：

1. 在 `third_party/rust/` 中添加 crate 源码
2. 使用 `gnrt`（GN Rust Tool）生成 GN 构建规则
3. 安全审计与许可证审查
4. 更新 `gnrt_config.toml` 管理依赖

> **与 Cargo 的差异**：Chromium 不直接使用 crates.io 解析依赖，而是 vendored + 手动生成 GN 规则，以确保可审计、可复现构建。

---

## 四、Bare Metal

### 4.1 no_std 与 alloc

Bare Metal Rust 通常从 `#![no_std]` 开始：

```rust,ignore
#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
```
- `#![no_std]`：禁用 `std`，仅保留 `core`
- `#![no_main]`：不提供默认入口，由链接脚本或启动代码接管
- `alloc`：若需要堆分配，需显式引入并设置全局分配器

### 4.2 微控制器：PAC → HAL → Board Support

嵌入式 Rust 的典型抽象栈：

```text
应用代码
  └── Board Support Package (BSP)      // 特定开发板封装
      └── Hardware Abstraction Layer (HAL) // 芯片级外设 Trait
          └── Peripheral Access Crate (PAC) // 寄存器级访问
              └── SVF/包厂商提供的 SVD
```
| 层级 | 示例 crate | 作用 |
|:---|:---|:---|
| PAC | `stm32f4xx-pac` | 直接映射寄存器 |
| HAL | `stm32f4xx-hal` | 实现 `embedded-hal` Trait |
| BSP | `nucleo-f401re` | 针对具体开发板封装 |

### 4.3 应用处理器与 UART 驱动

对于更复杂的 SoC / 应用处理器，Bare Metal 程序需要直接操作 MMIO：

```rust,ignore
use core::ptr::{read_volatile, write_volatile};

const UART_DR: *mut u32 = 0x0900_0000 as *mut u32;
const UART_FR: *mut u32 = 0x0900_0018 as *mut u32;

unsafe fn uart_putc(c: u8) {
    // 等待发送 FIFO 非满
    while read_volatile(UART_FR) & (1 << 5) != 0 {}
    write_volatile(UART_DR, c as u32);
}
```
> **安全要点**：MMIO 访问必须使用 `volatile` 读写，防止编译器优化掉硬件状态检查。

---

## 五、选型决策树

```text
是否需要与现有大型 C/C++ 代码库共存？
├── 是，Android AOSP 生态
│   └── 学习路径：Android.bp → AIDL → binder_rs → cxx/bindgen
├── 是，Chromium / 类似 GN 构建系统
│   └── 学习路径：GN rust_static_library → cxx → 第三方 crate 审计
├── 否，但有 OS（Linux/Windows/macOS）
│   └── 标准 cargo + FFI（bindgen/cxx 按需）
└── 否，无 OS 或 RTOS
    └── 学习路径：no_std → PAC/HAL → embedded-hal → 链接脚本
```
---

## 六、常见陷阱

| 场景 | 陷阱 | 应对 |
|:---|:---|:---|
| AOSP | 直接使用 crates.io 未审计 crate | 仅使用 AOSP 预置或自行审计后导入 `external/rust/crates/` |
| AOSP | AIDL 类型映射与 Rust 生命周期（Lifetimes）混淆 | 仔细阅读 AIDL Rust 后端生成的绑定文档 |
| Chromium | 手动写大量 `extern "C++"` | 优先使用 `cxx` 生成类型安全桥接 |
| Chromium | 未审计第三方 crate 许可证 | 使用 `gnrt` 并遵循 Chromium 引入流程 |
| Bare Metal | 在 `no_std` 中误用 `std` API | 使用 `core`/`alloc`，并通过 `cargo build --target` 验证 |
| Bare Metal | 非 volatile 访问 MMIO | 使用 `read_volatile` / `write_volatile` 或 `volatile-register` crate |

---

## 七、来源与延伸阅读

| 资源 | 适用场景 |
|:---|:---|
| [Google Comprehensive Rust — Android](https://google.github.io/comprehensive-rust/android.html) | AOSP Rust 入门 |
| [Google Comprehensive Rust — Chromium](https://google.github.io/comprehensive-rust/chromium.html) | Chromium Rust 与 GN/CXX |
| [Google Comprehensive Rust — Bare Metal](https://google.github.io/comprehensive-rust/bare-metal.html) | no_std、PAC、HAL、UART 驱动 |
| [AOSP Rust Documentation](https://security.googleblog.com/2021/05/integrating-rust-into-android-open.html) | 官方 AOSP Rust 指南 |
| [Chromium Rust Docs](https://chromium.googlesource.com/chromium/src/+/main/docs/rust.md) | Chromium Rust 策略与构建 |
| [The Embedded Rust Book](https://docs.rust-embedded.org/book/) | 通用嵌入式 Rust |
| [rust-embedded/awesome-embedded-rust](https://github.com/rust-embedded/awesome-embedded-rust) | 嵌入式 crate 生态 |

---

> **过渡**: 掌握平台集成后，可进一步阅读 [Industrial Case Studies](48_industrial_case_studies.md) 中的 Google Pixel 基带 Rust 集成、FSE 2026 AOSP 实证分析等案例，建立从理论到大规模工程实践的桥梁。
