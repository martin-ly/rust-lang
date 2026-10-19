# Rust POSIX/系统调用 crate 生态（canonical 缺口闭环页）

> **EN**: Rust POSIX & System-Call Crate Ecosystem (canonical gap-closure page)
> **Bloom 层级**: L3-L5
> **Summary**: crates.io `os` 分类（2,056 crates）的 canonical 生态页：rustix 1.1.5 零开销 unsafe-free 系统调用路线（linux-raw-sys 直 syscall、libc 仅 cfg 回退）、nix 0.31.3 高层 POSIX 封装、caps 0.5.6 Linux capabilities，附 rustix 12.7 亿下载量的传导来源实拆（tempfile/fd-lock 依赖链）与 libc 地位判读。本页补齐 W9 缺口扫描登记的「10 页顺带提及、0 专页」缺口（2026-10-19）。
> **受众**: [入门→进阶]
> **内容分级**: [专题级]
> **定位**: W9 建页队列②——全库 10 页顺带使用 nix/rustix 而无专页（01_process_model_and_lifecycle、07_process_security_and_sandboxing、02_advanced_process_management 等），本页为闭环裁决产物。
> **版本事实基线**: crates.io API 2026-10-19 实查；rustc 1.99.1。
> **前置概念**: [进程模型与生命周期](../../03_advanced/08_process_ipc/01_process_model_and_lifecycle.md) · [进程安全与沙箱](../../03_advanced/08_process_ipc/07_process_security_and_sandboxing.md) · [Rust vs Zig：系统级 ABI 对比（L5）](../../05_comparative/01_systems_languages/06_rust_vs_zig.md)
> **权威来源**: [rustix docs.rs](https://docs.rs/rustix/) · [nix docs.rs](https://docs.rs/nix/) · [crates.io os 分类](https://crates.io/categories/os) · [Rustonomicon — FFI（libc 回退与系统库绑定的 unsafe/ABI 官方口径）](https://doc.rust-lang.org/nomicon/ffi.html)（P0，2026-10-20 核验）

---

## 一、版图与实查锚点（crates.io 2026-10-19）

| crate | 版本（实查） | 累计下载 | 近期下载 | 判读 |
|:---|:---|---:|---:|:---|
| **rustix** | **1.1.5**（2026-09-16） | **12.7 亿** | 3.02 亿 | 系统层下载量之王（传导型，见 §三） |
| **nix** | **0.31.3**（2026-05-11） | 8.86 亿 | 2.07 亿 | 高层 POSIX 事实标准 |
| libc | （底层常驻） | — | — | 一切 POSIX 绑定的最终底座 |
| **caps** | **0.5.6**（2025-10-17） | 2,579 万 | 589 万 | Linux capabilities 专用件 |
| crates.io `os` 分类 | — | 2,056 crates | — | 分类口径实查 |

## 二、两条路线的语义分野

- **rustix（unsafe-free 直 syscall 路线）**：1.1.5 的依赖实拆显示其正常形态是 `linux-raw-sys 0.12`（unsafe 层 syscall/结构定义）之上包一层 safe API，Linux 主流 arch 上**不经 libc**；`libc ^0.2.182` 只在 `cfg(rustix_use_libc, miri, 非直-syscall arch)` 回退分支出现，Windows 走 `windows-sys`。设计卖点：无 libc 依赖、无动态分配、无 `unsafe` 出现在用户侧、1.x 线稳定。适合：自建 I/O 层、容器/沙箱工具、对供应链敏感（依赖树极小）的系统程序。
- **nix（高层 POSIX 语义路线）**：把 fork/exec/wait、信号、资源限额（`setrlimit`）、权限（`setuid/setgid`）、挂载、socket 选项等**语义化封装为 Rust 类型与 `nix::Result<Errno>`**。本库 10 页顺带引用的 nix 用例（进程限流、降权、seccomp 前置）都是这条路线。代价：依赖面比 rustix 宽、API 面广导致大量 API 长期藏在非默认 feature 门控后。

选型裁决：**要「直 syscall + 最小供应链」选 rustix；要「POSIX 语义齐、少写样板」选 nix**——两者不是竞争而是层次错位（rustix 近 syscall 层，nix 近 libc 语义层），容器/安全类项目常同时出现。

## 三、实查证据：rustix 12.7 亿下载量是「传导」不是「直接采用」

crates.io 依赖实拆：`tempfile 3.27.0` 与 `fd-lock 4.0.4` 的正常依赖都含 rustix——tempfile 是全库编译量级最大的临时文件件之一。结论：**rustix 的下载量主要经 tempfile 等基础设施传导**，评估生态权重必须区分直接采用与传递传导，直接套用「rustix 比 nix 流行 43%」的下载量对比会系统性高估其直接采用度。这是本页登记的判读陷阱①。

## 四、判读陷阱与生态事实

1. **libc 的隐形地位**：rustix 的 miri 回退分支、nix 的主体、以及大量 crate 仍直连 libc——「rustix 取代 libc」是夸大口径；实际是「Linux 直 syscall 场景多了一条不经 libc 的路线」。
2. **nix 的半稳定 API 门控**：nix 相当部分 API（如 sched、挂载、用户）藏在非默认 feature 门控后（按目标内核版本门控）——教程里「nix 没有 X」的断言常因读者没开该 feature 而失真。
3. **capabilities ≠ 降权**：caps（0.5.6）管理 Linux capability 集合，与 setuid 降权、no_new_privs、seccomp 是**四个正交机制**——安全加固页引用的 nix::unistd::setuid 与 caps 不可混为一谈（语义裁决见[进程安全与沙箱](../../03_advanced/08_process_ipc/07_process_security_and_sandboxing.md)）。

## 五、边界裁决

- 进程/信号/IPC 的**语义**（fork 危险、pid 管理、FD 传递）归 [08_process_ipc 组](../../03_advanced/08_process_ipc/01_process_model_and_lifecycle.md)；本页只裁 crate 生态与选型。
- 容器与 cgroup 工程线归[容器构建与交付流水线](../04_web_and_networking/12_container_build_and_delivery_pipeline.md)；内核内 Rust 归 [56 内核模块页](56_rust_for_linux_kernel_module_basics.md)（rust-for-Linux 不经任何用户态 syscall crate，是第四种形态）。

## 国际权威参考 / International Authority References

- [rustix GitHub（ByteStringe-rustix）](https://github.com/bytecodealliance/rustix) · [linux-raw-sys](https://github.com/bytecodealliance/linux-raw-sys)
- [nix GitHub（nix-rust/nix）](https://github.com/nix-rust/nix) · [caps GitHub（tails/rust-caps）](https://github.com/tails/rust-caps)
- [Linux capabilities(7) man](https://man7.org/linux/man-pages/man7/capabilities.7.html) · [POSIX.1-2017](https://pubs.opengroup.org/onlinepubs/9699919799/)
- 学术锚（2026-10-20 arXiv API 实核）：[Securing Mixed Rust with Hardware Capabilities (Yu, Han, Choudhury, Carlson, Saxena)](https://arxiv.org/abs/2507.03344)（2025-07-04 提交）——内存安全 Rust 与不安全底层组件混合时的硬件 capability 强制隔离，正对本页 rustix/nix「unsafe 直通 syscall 边界」与 capability 机制的交叉线。
- 学术锚（2026-10-20 arXiv API 实核）：[Friend or Foe Inside? Exploring In-Process Isolation to Maintain Memory Safety for Unsafe Rust (Gülmez, Nyman, Baumann, Mühlberg)](https://arxiv.org/abs/2306.08127)（2023-06-13 提交，v2）——unsafe Rust 的进程内隔离缓解实证，与 caps/setuid/no_new_privs/seccomp 正交机制讨论互参（进程安全语义见 [07_process_security_and_sandboxing](../../03_advanced/08_process_ipc/07_process_security_and_sandboxing.md)）。
