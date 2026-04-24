# build-std 使用指南与跟踪

## 什么是 build-std

`build-std` 是 Cargo 的一个实验性功能，允许在构建时从源码编译 Rust 标准库（`std`、`core`、`alloc`），而不是使用预编译的发行版标准库。

## 为什么需要 build-std

### 嵌入式场景

- **定制标准库**: 为特定目标裁剪 `std` 功能
- **no_std + alloc**: 在没有完整操作系统的环境中使用 `Vec`、`Box` 等
- **panic 策略**: 自定义 panic handler，避免栈展开开销
- **LTO 优化**: 对整个程序（包括标准库）进行链接时优化

### 体积优化

通过 `build-std` 配合 `panic = "abort"` 和 LTO，可以显著减小二进制体积：

- 去除未使用的 `std` 代码
- 内联标准库函数
- 自定义内存分配器

## 使用方法

### 1. 安装 nightly 工具链

```bash
rustup toolchain install nightly
rustup component add rust-src --toolchain nightly
```

### 2. 配置 cargo

在项目根目录的 `.cargo/config.toml` 中：

```toml
[unstable]
build-std = ["core", "alloc", "compiler_builtins"]
build-std-features = ["compiler-builtins-mem"]  # 使用 compiler-builtins 的 memcpy
```

### 3. 指定目标

```bash
cargo +nightly build -Z build-std=core,alloc --target thumbv7m-none-eabi
```

### 4. Cargo.toml 配置

```toml
[profile.release]
panic = "abort"
lto = true
opt-level = "z"
codegen-units = 1
```

## 稳定化进度跟踪

| 里程碑 | 状态 | 说明 |
|--------|------|------|
| 功能引入 | ✅ | 已作为 unstable 功能可用多年 |
| rust-src 组件 | ✅ | `rustup component add rust-src` 稳定可用 |
| Cargo.toml 原生支持 | ⏳ | 需在 `.cargo/config.toml` 中配置 |
| 无需 nightly | ⏳ | 仍需要 nightly toolchain 启用 `-Z build-std` |
| 完全稳定化 | 🔮 | 无明确时间表，依赖 Cargo 团队规划 |

### 当前替代方案

- **`#![no_std]` + `#![no_main]`**: 最稳定的方式，完全绕过标准库
- **`embedded-hal` 生态**: 提供跨平台 HAL 抽象
- **`cortex-m-rt`**: 提供启动代码和向量表

## HAL 设计模式深化

### 类型状态模式（Type State）

利用泛型将外设状态编码到类型中，编译时防止错误操作：

```rust
use core::marker::PhantomData;

pub struct Uninitialized;
pub struct Initialized;

pub struct Uart<STATE> {
    _state: PhantomData<STATE>,
}

impl Uart<Uninitialized> {
    pub fn new() -> Self { /* ... */ }
    pub fn init(self, baud: u32) -> Uart<Initialized> { /* ... */ }
}

impl Uart<Initialized> {
    pub fn send(&mut self, data: &[u8]) { /* ... */ }
}
```

### 寄存器访问模式

```rust
/// 类型安全的寄存器包装
pub struct Register<T> {
    ptr: *mut T,
}

impl<T> Register<T> {
    /// Volatile 读取
    pub unsafe fn read(&self) -> T {
        core::ptr::read_volatile(self.ptr)
    }

    /// Volatile 写入
    pub unsafe fn write(&mut self, value: T) {
        core::ptr::write_volatile(self.ptr, value);
    }

    /// 修改特定位
    pub unsafe fn modify<F>(&mut self, f: F)
    where
        F: FnOnce(T) -> T,
    {
        let current = self.read();
        self.write(f(current));
    }
}
```

## 参考

- [Cargo build-std 文档](https://doc.rust-lang.org/cargo/reference/unstable.html#build-std)
- [The Embedonomicon - build-std](https://docs.rust-embedded.org/embedonomicon/build-std.html)
- [Rust Embedded Working Group](https://github.com/rust-embedded/wg)
