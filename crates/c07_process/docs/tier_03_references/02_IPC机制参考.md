# Tier 3: IPC机制参考

> **文档类型**: 技术参考  
> **适用版本**: Rust 1.90+

---

## IPC机制分类

**数据传输类**:

- 管道 (Pipe)
- 命名管道 (FIFO)
- 套接字 (Socket)

**共享数据类**:

- 共享内存 (Shared Memory)
- 内存映射文件 (mmap)

**同步通信类**:

- 信号 (Signal)
- 消息队列 (Message Queue)

---

## 性能对比

| 机制 | 延迟 | 吞吐量 | 实现复杂度 |
|------|------|--------|-----------|
| 管道 | 中 | 中 | 低 |
| Unix Socket | 低 | 高 | 中 |
| TCP Socket | 中 | 中 | 中 |
| 共享内存 | 最低 | 最高 | 高 |

---

## Rust实现库

- **标准库**: `std::process`, `std::net`
- **Unix**: `nix`, `unix_socket`
- **共享内存**: `shared_memory`, `memmap2`
- **消息队列**: `crossbeam-channel`, `ipc-channel`

---

**参考**: [IPC通信实践](../tier_02_guides/02_IPC通信实践.md)

---

**文档维护**: Documentation Team  
**创建日期**: 2025-10-22
