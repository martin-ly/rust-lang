# Rust 扩展主题导航

欢迎来到 Rust 扩展主题文档集。本文档涵盖了 Rust 编程语言的高级特性和专业应用领域，为已经掌握 Rust 基础的开发者提供深入的技术指导。

## 文档结构

本文档集包含以下六个核心主题：

### 1. [FFI 互操作性](./ffi-interoperability.md)

探索 Rust 与外部代码（特别是 C 语言）的交互能力：

- **C 语言绑定**：使用 `extern` 关键字和 FFI 调用 C 库
- **Python 绑定**：通过 PyO3 创建 Python 扩展模块
- **回调函数**：在 Rust 中处理 C 风格的回调
- **内存布局对齐**：确保跨语言数据结构兼容性

**适用场景**：系统编程、遗留系统集成、性能关键型库开发

### 2. [过程宏开发](./proc-macros.md)

掌握 Rust 元编程的核心技术：

- **Derive 宏**：自动为结构体和枚举实现 trait
- **属性宏**：自定义代码转换和注解处理
- **函数式宏**：创建 DSL 和自定义语法
- **Token 操作**：直接操作编译器的词法分析树

**适用场景**：框架开发、代码生成、DSL 设计、自动化 trait 实现

### 3. [Unsafe Rust 模式](./unsafe-rust-patterns.md)

深入理解 Rust 的底层编程能力：

- **原始指针操作**：`*const T` 和 `*mut T` 的使用
- **Union 类型**：C 风格联合体的 Rust 实现
- **内联汇编**：`asm!` 和 `naked_asm!` 宏的使用
- **FFI 边界安全**：Safe 包装器设计模式

**适用场景**：系统编程、嵌入式开发、性能优化、操作系统内核

### 4. [No_std 开发](./no-std-development.md)

在资源受限环境中使用 Rust：

- **嵌入式系统**：ARM Cortex-M 和 RISC-V 目标
- **操作系统内核**：裸机编程和引导加载程序
- **自定义分配器**：实现 `GlobalAlloc` trait
- **panic 处理**：自定义 panic 处理器实现

**适用场景**：物联网设备、实时系统、引导程序、微控制器

### 5. [Rust for Linux](./rust-for-linux.md)

参与 Linux 内核的 Rust 支持开发：

- **内核模块编写**：使用 Rust 编写可加载内核模块
- **eBPF 程序**：使用 Aya 框架开发 eBPF 应用
- **内核 API 绑定**：与 Linux 内核 C API 交互
- **驱动程序开发**：字符设备和块设备驱动

**适用场景**：Linux 内核开发、系统级驱动、网络过滤、性能监控

## 学习路径建议

### 初学者路径

如果你是 Rust 中级开发者，建议按以下顺序学习：

1. **FFI 互操作性** → 理解 Rust 如何与现有生态集成
2. **过程宏** → 掌握代码生成和元编程
3. **Unsafe Rust** → 了解 Rust 的安全边界和底层能力

### 专业开发者路径

针对特定领域的开发者：

- **嵌入式/系统开发者**：No_std → Unsafe Rust → Rust for Linux
- **工具链/框架开发者**：过程宏 → FFI 互操作性 → Unsafe Rust
- **内核开发者**：Rust for Linux → No_std → Unsafe Rust

### 学习进度检查点

#### FFI 阶段检查点

- [ ] 成功调用 C 标准库函数
- [ ] 使用 bindgen 生成复杂 C 库的绑定
- [ ] 实现安全的 C 库包装器
- [ ] 创建可以被 C 调用的 Rust 库
- [ ] 处理回调函数和复杂数据结构

#### 过程宏阶段检查点

- [ ] 实现简单的 derive 宏
- [ ] 使用属性宏处理函数参数
- [ ] 创建函数式宏（如 DSL）
- [ ] 理解 TokenStream 的解析和生成
- [ ] 使用 syn 进行复杂的 AST 操作

#### Unsafe Rust 阶段检查点

- [ ] 正确使用原始指针进行内存操作
- [ ] 实现自定义智能指针
- [ ] 使用 MaybeUninit 进行延迟初始化
- [ ] 编写内联汇编代码
- [ ] 理解内存排序和原子操作

#### No_std 阶段检查点

- [ ] 创建基本的 no_std 项目
- [ ] 实现自定义 panic 处理器
- [ ] 编写全局分配器
- [ ] 在嵌入式设备上运行 Rust 代码
- [ ] 理解链接器脚本和启动代码

#### Rust for Linux 阶段检查点

- [ ] 编译支持 Rust 的 Linux 内核
- [ ] 编写并加载内核模块
- [ ] 实现字符设备驱动
- [ ] 使用 eBPF 进行网络过滤
- [ ] 调试内核代码

## 前置知识要求

在学习这些扩展主题之前，请确保你已经掌握：

- Rust 所有权系统和生命周期
- Trait 系统和泛型编程
- 错误处理（Result/Option）
- 模块系统和 Cargo 工作流
- 基础的并发编程概念

### 推荐的 Rust 水平

- **中级（Intermediate）**：能够理解复杂的 trait bound 和生命周期标注
- **高级（Advanced）**：能够设计泛型 API 和自定义数据结构
- **专家（Expert）**：理解编译器内部工作原理和 LLVM IR

## 环境准备

### 基础工具链

```bash
# 安装 Rust 稳定版
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 添加必要的目标
rustup target add thumbv7m-none-eabi      # ARM Cortex-M3
rustup target add riscv64gc-unknown-none-elf  # RISC-V
rustup target add wasm32-unknown-unknown   # WebAssembly

# 安装 nightly 工具链（用于过程宏和某些实验性功能）
rustup install nightly
rustup component add rust-src --toolchain nightly
```

### Linux 内核开发环境

```bash
# 克隆支持 Rust 的 Linux 内核
git clone https://github.com/Rust-for-Linux/linux.git
cd linux

# 启用 Rust 支持
make menuconfig  # 选择 General setup -> Rust support

# 编译带有 Rust 模块的内核
make LLVM=1 -j$(nproc)
```

### eBPF 开发环境

```bash
# 安装 Aya 工具链
cargo install bpf-linker
cargo install cargo-generate

# 生成 eBPF 项目模板
cargo generate --name my-ebpf-project https://github.com/aya-rs/aya-template
```

### 嵌入式开发环境

```bash
# 安装 ARM 工具链
rustup target add thumbv7m-none-eabi thumbv7em-none-eabihf

# 安装 OpenOCD 用于调试
sudo apt install openocd gdb-multiarch

# 安装 cargo-embed（替代 OpenOCD 的简便方案）
cargo install cargo-embed
```

## 代码示例索引

每个文档都包含大量可直接运行的代码示例：

| 文档 | 主要示例项目 |
|------|-------------|
| FFI | `libsqlite3-sys`, `pyo3-example`, `callback-demo` |
| 过程宏 | `derive-builder`, `route-macro`, `sql!` DSL |
| Unsafe | `raw-pointer-vec`, `union-parser`, `asm-syscall` |
| No_std | `cortex-m-rt`, `custom-alloc`, `kernel-hello` |
| Rust for Linux | `rust-scull`, `rust-ebpf-filter` |

## 安全警告

⚠️ **重要提示**：

1. **Unsafe Rust** 文档中的代码需要特别小心，不当使用会导致未定义行为
2. **FFI 互操作性**需要确保跨语言内存管理正确
3. **内核代码**的错误可能导致系统崩溃或安全漏洞
4. 在生产环境中使用这些技术前，请进行充分的测试和审计

### 安全最佳实践

```rust
// 1. 最小化 unsafe 代码块
pub fn safe_wrapper() -> Result<(), Error> {
    // 验证前置条件
    if !precondition_met() {
        return Err(Error::InvalidState);
    }

    // 执行 unsafe 操作
    unsafe {
        // 最小化的 unsafe 代码
        raw_operation()
    }
}

// 2. 文档化安全契约
/// # Safety
/// - 调用者必须确保 ptr 是有效的非空指针
/// - ptr 在调用期间必须保持有效
unsafe fn raw_operation(ptr: *mut Data) {
    // ...
}
```

## 贡献指南

欢迎对本文档集进行贡献：

1. 代码示例应包含完整的 Cargo.toml 配置
2. 每个主题需要包含 "常见陷阱" 和 "最佳实践" 章节
3. 外部链接应指向官方或权威来源
4. 使用 `cargo clippy` 和 `cargo fmt` 确保代码质量

### 提交 Issue

如果你发现以下问题，请提交 Issue：

- 代码示例无法编译或运行
- 文档中的错误或不清晰之处
- 过时的信息或链接
- 安全相关的问题

### 提交 Pull Request

1. Fork 本仓库
2. 创建你的特性分支 (`git checkout -b feature/amazing-feature`)
3. 提交你的更改 (`git commit -m 'Add some amazing feature'`)
4. 推送到分支 (`git push origin feature/amazing-feature`)
5. 打开一个 Pull Request

## 参考资源

### 官方文档

- [The Rust Programming Language - Advanced Topics](https://doc.rust-lang.org/book/)
- [The Rustonomicon](https://doc.rust-lang.org/nomicon/) - Unsafe Rust 权威指南
- [The Rust Reference](https://doc.rust-lang.org/reference/)
- [Rust for Linux Documentation](https://rust-for-linux.com/)

### 社区资源

- [Rust Embedded Working Group](https://github.com/rust-embedded/wg)
- [Aya eBPF 框架](https://aya-rs.dev/)
- [PyO3 文档](https://pyo3.rs/)
- [Bindgen 用户指南](https://rust-lang.github.io/rust-bindgen/)

### 相关书籍

- 《Programming Rust》第 2 版 - Jim Blandy 等
- 《Rust for Rustaceans》 - Jon Gjengset
- 《Hands-On Rust》 - Herbert Wolverson
- 《Linux Kernel Development》第 3 版 - Robert Love
- 《Embedded Rust》 - Jonathan Pallant

### 在线课程

- [Rust 嵌入式编程](https://docs.rust-embedded.org/)
- [Rust 操作系统开发](https://os.phil-opp.com/)
- [Rust 系统编程](https://www.youtube.com/playlist?list=PLai5B987bY9b07nQZ1t1KY7mYd6rJc6fB)

## 版本信息

本文档集基于以下工具版本编写：

- Rust: 1.75.0+
- Cargo: 1.75.0+
- Linux Kernel: 6.7+ (with Rust support)
- PyO3: 0.20+
- Aya: 0.12+
- bindgen: 0.69+
- cortex-m-rt: 0.7+

### 更新计划

- 每季度检查文档中的链接和代码示例
- 跟随 Rust 新版本更新特性说明
- 根据社区反馈添加新的主题和示例

## 术语表

| 术语 | 解释 |
|------|------|
| FFI | Foreign Function Interface，外部函数接口 |
| ABI | Application Binary Interface，应用程序二进制接口 |
| DSL | Domain Specific Language，领域特定语言 |
| LTO | Link Time Optimization，链接时优化 |
| PIC | Position Independent Code，位置无关代码 |
| eBPF | Extended Berkeley Packet Filter，扩展伯克利包过滤器 |
| Kprobe | Kernel Probe，内核探针 |
| Uprobe | User-space Probe，用户空间探针 |
| HAL | Hardware Abstraction Layer，硬件抽象层 |
| MMU | Memory Management Unit，内存管理单元 |
| DMA | Direct Memory Access，直接内存访问 |
| IRQ | Interrupt Request，中断请求 |
| ISR | Interrupt Service Routine，中断服务程序 |
| SoC | System on Chip，片上系统 |
| MCU | Microcontroller Unit，微控制器单元 |

## 常见问题

### Q: 我需要多深的 Rust 知识才能学习这些主题？

A: 建议至少完成《Rust 程序设计语言》的学习，并有一些实际项目经验。理解生命周期、trait 和错误处理是基础。

### Q: 这些技术在实际工作中用得多吗？

A: 取决于你的领域：

- FFI：几乎所有需要与 C/C++ 库集成的项目都会用到
- 过程宏：框架和库开发者经常使用
- Unsafe：系统编程和性能关键代码必需
- No_std：嵌入式和内核开发必备
- Rust for Linux：新兴领域，机会很多

### Q: 学习这些主题的推荐时间投入？

A:

- FFI：1-2 周
- 过程宏：2-3 周
- Unsafe Rust：3-4 周
- No_std：4-6 周
- Rust for Linux：6-8 周

### Q: 如何获得帮助？

A:

- Rust 官方 Discord 和论坛
- Stack Overflow [rust] 标签
- 各主题的专门社区（如 Rust Embedded Matrix 频道）
- 本文档的 Issue 区

---

*最后更新：2026年3月4日*

*文档维护：Rust 扩展主题工作组*

*许可证：MIT OR Apache-2.0*
