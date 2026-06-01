//! Zero Copy Networking

#![forbid(unsafe_code)]

//! 零拷贝网络编程概念解析
//! network programming concept

use std::io;

// ============================================================================
// 1. Sendfile 概念
// ============================================================================

/// `sendfile` 零拷贝文件传输概念
/// `sendfile` transmission concept
/// `sendfile` 零拷贝文件transmissionconcept
pub struct SendfileConcept;

impl SendfileConcept {
    /// sendfile 概述
    pub fn concept() -> &'static str {
        r#"=== sendfile 零拷贝文件传输 ===

核心思想：
- 在文件描述符和 socket 描述符之间直接传输数据
- 数据无需经过用户态缓冲区，全程在内核态完成拷贝

传统流程（4 次拷贝，4 次上下文切换）：
1. 磁盘 -> 内核页缓存（DMA 拷贝）
2. 内核页缓存 -> 用户缓冲区（CPU 拷贝）
3. 用户缓冲区 -> 内核 socket 缓冲区（CPU 拷贝）
4. 内核 socket 缓冲区 -> 网卡（DMA 拷贝）

sendfile 流程（2 次拷贝，2 次上下文切换）：
1. 磁盘 -> 内核页缓存（DMA 拷贝）
2. 内核页缓存 -> 网卡（DMA 拷贝，通过 DMA gather）

优势：
- 减少 50% 的数据拷贝次数
- 减少 50% 的上下文切换
- 降低 CPU 占用和内存带宽压力

限制：
- 仅适用于文件到 socket 的传输
- 需要操作系统支持（Linux 2.1+）
- 不能对传输数据进行修改（如加密、压缩）
"#
    }

    pub fn rust_usage() -> &'static str {
        r#"=== Rust 中的 sendfile 概念 ===

Rust 标准库不直接暴露 sendfile 系统调用，
但可以通过以下方式实现零拷贝或近零拷贝文件传输：

1. `std::os::unix::fs::FileExt::sendfile`（第三方封装）
2. `tokio::net::TcpStream` + `tokio::fs::File` 配合 `sendfile` 封装
3. 使用 `io_uring` 的 `opcode::Send` 与固定缓冲区

注意：由于本仓库禁止 unsafe 代码，以下仅为概念说明。
真实实现需要调用 libc::sendfile 或使用 nix crate。
"#
    }
}

// ============================================================================
// 2. mmap + 网络概念
// ============================================================================

pub struct MmapNetworkConcept;

impl MmapNetworkConcept {
    /// mmap 网络应用概念
    /// mmap network application concept
    pub fn concept() -> &'static str {
        r#"=== mmap + 网络概念 ===

mmap（内存映射文件）在网络场景中的应用：

1. 静态文件服务
   - 将大文件映射到进程地址空间
   - 网络层直接读取映射区域发送，避免 read() 拷贝
   - 配合 sendfile 可进一步减少拷贝

2. 零拷贝接收
   - 某些高性能网卡驱动支持将接收缓冲区映射到用户态
   - 应用程序直接访问网卡 DMA 缓冲区，无需内核拷贝

3. 共享内存 IPC
   - 同一主机上的进程间通信可通过 mmap 共享区域实现
   - 配合 Unix Domain Socket 传递元数据

Rust 中的相关 API：
- `memmap2::Mmap` / `memmap2::MmapMut`（第三方 crate）
- `std::fs::File` 配合 `std::os::unix::fs::FileExt`

限制：
- mmap 区域的大小和生命周期管理较复杂
- 大文件映射可能触发 OOM（尤其在 32 位系统）
- 需要处理页错误和缓存一致性问题
"#
    }
}

// ============================================================================
// 3. io_uring 概念概述
// ============================================================================

/// io_uring 概念概述
/// io_uring concept
pub struct IoUringConcept;

impl IoUringConcept {
    /// io_uring 总览
    pub fn overview() -> &'static str {
        r#"=== io_uring 零拷贝异步 I/O ===

io_uring 是 Linux 内核 5.1+ 引入的异步 I/O 接口：

核心组件：
- Submission Queue (SQ)：用户态提交 I/O 请求
- Completion Queue (CQ)：内核态返回 I/O 结果
- 共享内存映射：SQ/CQ 与内核共享，减少 syscall

零拷贝特性：
1. Registered Buffers
   - 预先注册用户态缓冲区到内核
   - I/O 操作直接使用已注册缓冲区，避免每次 pin/unpin

2. Fixed Files
   - 预先注册文件描述符
   - 后续操作使用索引而非 fd，减少内核查找

3. 无需系统调用（Polling 模式）
   - 开启 IORING_SETUP_SQPOLL 后，内核线程轮询 SQ
   - 用户态只需写入 SQ，无需 enter syscall

适用场景：
- 高并发网络服务器（如反向代理、缓存）
- 高频小 I/O 的数据库/存储系统
- 需要极致延迟敏感的应用
"#
    }

    /// io_uring and epoll 零拷贝差异
    pub fn vs_epoll() -> &'static str {
        r#"=== io_uring vs epoll（零拷贝角度） ===

| 特性           | epoll                | io_uring                     |
|----------------|----------------------|------------------------------|
| 通知模式       | 就绪通知             | 完成通知                     |
| 缓冲区管理     | 用户态预分配         | 支持 registered buffers      |
| 文件 I/O       | 同步 fallback        | 真正异步                     |
| 批量提交       | 每次一个             | 批量，可零 syscall           |
| 零拷贝支持     | 需配合 sendfile      | 原生支持（registered buf）   |
| 可移植性       | Linux                | Linux 5.1+                   |

结论：
- 纯网络 I/O 且需跨平台 → Tokio（底层自动选择）
- 仅 Linux + 追求极致性能 → io_uring
"#
    }
}

// ============================================================================
// 4. Rust 零拷贝 API 对比
// ============================================================================

/// Rust 零拷贝 API 对比
/// Rust API to
pub struct ZeroCopyApiComparison;

impl ZeroCopyApiComparison {
    /// std::io::copy
    pub fn std_io_copy() -> &'static str {
        r#"=== std::io::copy ===

签名：`pub fn copy<R, W>(reader: &mut R, writer: &mut W) -> Result<u64>`

实现原理：
- 内部使用 8KB 缓冲区循环读取和写入
- 数据必须经过用户态缓冲区（至少 2 次内核态拷贝）

适用场景：
- 通用、跨平台、无需极致性能
- 需要对数据进行中间处理（如统计、转换）

性能：
- 有用户态缓冲开销
- 非零拷贝
"#
    }

    /// tokio::io::copy_bidirectional
    pub fn tokio_copy_bidirectional() -> &'static str {
        r#"=== tokio::io::copy_bidirectional ===

签名：`pub async fn copy_bidirectional<A, B>(a: &mut A, b: &mut B) -> Result<(u64, u64)>`

实现原理：
- 使用两个缓冲区分别处理 A->B 和 B->A 方向
- 异步调度，支持背压和取消安全
- 底层在 Linux 上可能使用 sendfile（取决于实现版本）

适用场景：
- 代理、转发、隧道场景
- 需要同时处理双向流

性能：
- 仍使用用户态缓冲（除非内部优化使用 sendfile）
- 优势在于异步并发，而非单次拷贝零开销
"#
    }

    /// API 对比总结
    /// API to summary
    /// API to比summary
    pub fn comparison() -> &'static str {
        r#"=== Rust 零拷贝 API 对比总结 ===

| API                        | 零拷贝 | 异步 | 双向 | 适用场景           |
|----------------------------|--------|------|------|-------------------|
| std::io::copy              | ❌     | ❌   | ❌   | 简单文件拷贝       |
| tokio::io::copy            | ❌     | ✅   | ❌   | 异步流拷贝         |
| tokio::io::copy_bidirectional | ❌  | ✅   | ✅   | 代理/转发          |
| sendfile (libc)            | ✅     | ❌   | ❌   | 文件->Socket       |
| io_uring + registered buf  | ✅     | ✅   | ✅   | 极致性能 Linux 服务|

建议：
- 优先使用 Tokio 的高级抽象，获得可移植性和正确性
- 在已验证的瓶颈处，针对性地引入 sendfile 或 io_uring
"#
    }
}

/// 真实零拷贝需要 unsafe 或平台特定 API，此处仅作语义演示。
/// real unsafe or platform API，this demonstration 。
pub fn simulate_zero_copy_transfer(
    reader: &mut impl io::Read,
    writer: &mut impl io::Write,
) -> io::Result<u64> {
    io::copy(reader, writer)
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sendfile_concept() {
        let doc = SendfileConcept::concept();
        assert!(doc.contains("sendfile"));
        assert!(doc.contains("DMA"));
    }

    #[test]
    fn test_mmap_network_concept() {
        let doc = MmapNetworkConcept::concept();
        assert!(doc.contains("mmap"));
        assert!(doc.contains("静态文件服务"));
    }

    #[test]
    fn test_io_uring_overview() {
        let doc = IoUringConcept::overview();
        assert!(doc.contains("io_uring"));
        assert!(doc.contains("Submission Queue"));
    }

    #[test]
    fn test_io_uring_vs_epoll() {
        let doc = IoUringConcept::vs_epoll();
        assert!(doc.contains("epoll"));
    }

    #[test]
    fn test_std_io_copy_doc() {
        let doc = ZeroCopyApiComparison::std_io_copy();
        assert!(doc.contains("std::io::copy"));
    }

    #[test]
    fn test_tokio_copy_bidirectional_doc() {
        let doc = ZeroCopyApiComparison::tokio_copy_bidirectional();
        assert!(doc.contains("tokio::io::copy_bidirectional"));
    }

    #[test]
    fn test_api_comparison_doc() {
        let doc = ZeroCopyApiComparison::comparison();
        assert!(doc.contains("零拷贝"));
    }

    #[test]
    fn test_simulate_zero_copy_transfer() {
        let mut input: &[u8] = b"hello zero-copy";
        let mut output = Vec::new();
        let n = simulate_zero_copy_transfer(&mut input, &mut output).unwrap();
        assert_eq!(n, 15);
        assert_eq!(output, b"hello zero-copy");
    }
}
