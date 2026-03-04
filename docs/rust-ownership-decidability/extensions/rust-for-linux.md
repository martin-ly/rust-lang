# Rust for Linux

Rust for Linux 是一个将 Rust 编程语言引入 Linux 内核的开源项目。
本章节详细介绍如何使用 Rust 编写 Linux 内核模块、eBPF 程序以及与现有内核基础设施的集成。

## 目录

- [Rust for Linux](#rust-for-linux)
  - [目录](#目录)
  - [项目概述](#项目概述)
    - [为什么选择 Rust for Linux](#为什么选择-rust-for-linux)
    - [当前状态](#当前状态)
  - [环境搭建](#环境搭建)
    - [系统要求](#系统要求)
    - [编译支持 Rust 的内核](#编译支持-rust-的内核)
    - [配置检查](#配置检查)
  - [内核模块开发](#内核模块开发)
    - [Hello World 模块](#hello-world-模块)
    - [模块参数](#模块参数)
  - [字符设备驱动](#字符设备驱动)
    - [基础字符设备](#基础字符设备)
    - [使用 ioctl](#使用-ioctl)
  - [块设备驱动](#块设备驱动)
    - [简单的 RAM 磁盘](#简单的-ram-磁盘)
  - [网络子系统](#网络子系统)
    - [网络设备驱动](#网络设备驱动)
  - [eBPF 开发](#ebpf-开发)
    - [Aya 框架入门](#aya-框架入门)
    - [XDP 程序](#xdp-程序)
    - [Kprobe 跟踪](#kprobe-跟踪)
    - [使用 eBPF 映射](#使用-ebpf-映射)
    - [TC (流量控制) 程序](#tc-流量控制-程序)
  - [调试和测试](#调试和测试)
    - [内核调试](#内核调试)
    - [使用 GDB](#使用-gdb)
    - [eBPF 调试](#ebpf-调试)

## 项目概述

### 为什么选择 Rust for Linux

Linux 内核开发传统上使用 C 语言，但 C 语言存在内存安全问题：

- 大约 70% 的内核安全漏洞与内存安全相关
- 复杂的并发编程容易出错
- 缺乏现代类型系统支持

Rust 提供了：

- 编译时内存安全检查
- 零成本抽象
- fearless 并发
- 现代工具链

### 当前状态

截至 Linux 6.7+：

- Rust 支持已合并到主线内核
- 基本的驱动程序框架可用
- 网络、块设备和字符设备支持
- 与 C 代码的互操作性

## 环境搭建

### 系统要求

```bash
# 安装依赖（Ubuntu/Debian）
sudo apt update
sudo apt install -y \
    build-essential \
    llvm \
    clang \
    lld \
    rustup \
    bindgen \
    libssl-dev \
    flex bison \
    libelf-dev \
    libncurses-dev

# 安装 Rust
rustup update
rustup component add rust-src
rustup target add x86_64-unknown-none
```

### 编译支持 Rust 的内核

```bash
# 克隆 Linux 内核源码
git clone https://github.com/torvalds/linux.git
cd linux

# 或使用 Rust for Linux 分支
git clone https://github.com/Rust-for-Linux/linux.git
cd linux

# 配置内核
make menuconfig

# 启用以下选项：
# General setup -> Rust support
# Kernel hacking -> Rust hacking

# 编译
make LLVM=1 -j$(nproc)

# 安装模块
sudo make modules_install
sudo make install
```

### 配置检查

```bash
# 检查 Rust 支持
make rustavailable

# 检查绑定生成
make rust/bindings/patched
```

## 内核模块开发

### Hello World 模块

**rust_hello.rs:**

```rust
//! Hello World 内核模块示例

use kernel::prelude::*;
use kernel::module;

module! {
    type: RustHello,
    name: b"rust_hello",
    author: b"Your Name",
    description: b"A simple hello world kernel module in Rust",
    license: b"GPL",
}

struct RustHello;

impl kernel::Module for RustHello {
    fn init(_module: &'static ThisModule) -> Result<Self> {
        pr_info!("Hello from Rust kernel module!\n");
        Ok(RustHello)
    }
}

impl Drop for RustHello {
    fn drop(&mut self) {
        pr_info!("Goodbye from Rust kernel module!\n");
    }
}
```

**Makefile:**

```makefile
obj-$(CONFIG_RUST_HELLO) += rust_hello.o

# 指定 Rust 源文件
rust_hello-objs := rust_hello.rs
```

**Kconfig:**

```kconfig
config RUST_HELLO
    tristate "Rust Hello World module"
    depends on RUST
    help
      This is a simple hello world kernel module written in Rust.
```

### 模块参数

```rust
use kernel::prelude::*;
use kernel::module;
use kernel::module_param;

module! {
    type: RustParam,
    name: b"rust_param",
    author: b"Your Name",
    description: b"Module with parameters",
    license: b"GPL",
    params: {
        count: i32 {
            default: 1,
            permissions: 0o644,
            description: b"Number of times to print",
        },
        message: str {
            default: b"Hello",
            permissions: 0o644,
            description: b"Message to print",
        },
    },
}

struct RustParam {
    count: i32,
}

impl kernel::Module for RustParam {
    fn init(_module: &'static ThisModule) -> Result<Self> {
        // 访问模块参数
        let count = *module_param::read_lock!(count);
        let message = module_param::read_lock!(message);

        for i in 0..count {
            pr_info!("{} {}\n", message, i);
        }

        Ok(RustParam { count })
    }
}
```

## 字符设备驱动

### 基础字符设备

```rust
//! Rust 字符设备驱动示例

use kernel::prelude::*;
use kernel::file::File;
use kernel::io_buffer::{IoBufferReader, IoBufferWriter};
use kernel::miscdev::MiscDevice;
use kernel::sync::{Arc, Mutex};
use kernel::uaccess::UserSlicePtr;

module! {
    type: RustCharDev,
    name: b"rust_char_dev",
    author: b"Your Name",
    description: b"Rust character device driver",
    license: b"GPL",
}

// 设备状态
struct DeviceData {
    buffer: Vec<u8>,
    read_pos: usize,
}

impl DeviceData {
    fn new() -> Self {
        DeviceData {
            buffer: Vec::new(),
            read_pos: 0,
        }
    }
}

// 文件操作实现
#[vtable]
impl kernel::file::Operations for RustCharDev {
    type Data = Arc<Mutex<DeviceData>>;
    type OpenData = ();

    fn open(_data: &(), _file: &File) -> Result<Self::Data> {
        pr_info!("RustCharDev: open\n");
        Ok(Arc::new(Mutex::new(DeviceData::new())))
    }

    fn read(
        data: Self::Data,
        _file: &File,
        writer: &mut impl IoBufferWriter,
        offset: u64,
    ) -> Result<usize> {
        let mut device_data = data.lock();

        if offset as usize >= device_data.buffer.len() {
            return Ok(0); // EOF
        }

        let remaining = &device_data.buffer[offset as usize..];
        let to_write = writer.len().min(remaining.len());

        writer.write_slice(&remaining[..to_write])?;

        Ok(to_write)
    }

    fn write(
        data: Self::Data,
        _file: &File,
        reader: &mut impl IoBufferReader,
        _offset: u64,
    ) -> Result<usize> {
        let mut device_data = data.lock();

        // 读取用户数据
        let len = reader.len();
        let mut buf = vec![0u8; len];
        reader.read_slice(&mut buf)?;

        // 存储数据
        device_data.buffer.extend_from_slice(&buf);

        pr_info!("RustCharDev: wrote {} bytes\n", len);
        Ok(len)
    }

    fn release(_data: Self::Data, _file: &File) {
        pr_info!("RustCharDev: release\n");
    }
}

struct RustCharDev {
    _dev: Pin<Box<MiscDevice>>,
}

impl kernel::Module for RustCharDev {
    fn init(_module: &'static ThisModule) -> Result<Self> {
        pr_info!("RustCharDev: init\n");

        let dev = MiscDevice::new(
            kernel::c_str!("rust_char"),
            Arc::new(Mutex::new(DeviceData::new())),
        )?;

        Ok(RustCharDev { _dev: dev })
    }
}
```

### 使用 ioctl

```rust
use kernel::ioctl;

// 定义 ioctl 命令
const RUST_IOC_MAGIC: u8 = b'r';

ioctl::define_ioctl! {
    /// 获取缓冲区大小
    GET_BUFFER_SIZE = ioctl::read::<u32>, RUST_IOC_MAGIC, 0x00;

    /// 清空缓冲区
    CLEAR_BUFFER = ioctl::none, RUST_IOC_MAGIC, 0x01;

    /// 设置配置
    SET_CONFIG = ioctl::write::<DeviceConfig>, RUST_IOC_MAGIC, 0x02;
}

#[repr(C)]
#[derive(Default)]
struct DeviceConfig {
    max_size: u32,
    flags: u32,
}

unsafe impl ioctl::IoctlCommand for DeviceConfig {
    const fn metadata() -> ioctl::IoctlCmd {
        ioctl::IoctlCmd {
            dir: ioctl::Direction::Write,
            size: core::mem::size_of::<Self>(),
        }
    }
}

#[vtable]
impl kernel::file::Operations for RustIoctlDev {
    // ... 其他实现 ...

    fn ioctl(
        data: Self::Data,
        _file: &File,
        cmd: &mut kernel::ioctl::Command,
    ) -> Result<i32> {
        match cmd.cmd() {
            GET_BUFFER_SIZE => {
                let device_data = data.lock();
                let size = device_data.buffer.len() as u32;
                cmd.arg::<u32>().write(&size)?;
                Ok(0)
            }
            CLEAR_BUFFER => {
                let mut device_data = data.lock();
                device_data.buffer.clear();
                device_data.read_pos = 0;
                Ok(0)
            }
            SET_CONFIG => {
                let config = cmd.arg::<DeviceConfig>().read()?;
                let mut device_data = data.lock();
                device_data.max_size = config.max_size as usize;
                Ok(0)
            }
            _ => Err(EINVAL),
        }
    }
}
```

## 块设备驱动

### 简单的 RAM 磁盘

```rust
//! Rust 块设备驱动 - RAM 磁盘

use kernel::prelude::*;
use kernel::block::{self, BlockDevice, BlockDeviceHolder, BlockOperations};
use kernel::sync::{Arc, Mutex};
use kernel::io::{self, IoFlags};

module! {
    type: RustRamDisk,
    name: b"rust_ramdisk",
    author: b"Your Name",
    description: b"RAM disk block device in Rust",
    license: b"GPL",
}

const SECTOR_SIZE: usize = 512;
const NUM_SECTORS: usize = 1024 * 1024; // 512 MB

struct RamDisk {
    data: Mutex<Vec<u8>>,
}

impl RamDisk {
    fn new() -> Result<Self> {
        let data = vec![0u8; SECTOR_SIZE * NUM_SECTORS];
        Ok(RamDisk {
            data: Mutex::new(data),
        })
    }

    fn read(&self, sector: usize, buf: &mut [u8]) -> Result<()> {
        let data = self.data.lock();
        let offset = sector * SECTOR_SIZE;

        if offset + buf.len() > data.len() {
            return Err(EINVAL);
        }

        buf.copy_from_slice(&data[offset..offset + buf.len()]);
        Ok(())
    }

    fn write(&self, sector: usize, buf: &[u8]) -> Result<()> {
        let mut data = self.data.lock();
        let offset = sector * SECTOR_SIZE;

        if offset + buf.len() > data.len() {
            return Err(EINVAL);
        }

        data[offset..offset + buf.len()].copy_from_slice(buf);
        Ok(())
    }
}

#[vtable]
impl BlockOperations for RamDisk {
    type Data = Arc<RamDisk>;

    fn open(_disk: &Self::Data) -> Result {
        Ok(())
    }

    fn release(_disk: &Self::Data) {}

    fn io_submit(disk: &Self::Data, bio: &mut block::Bio) -> Result {
        let rw = bio.bi_rw();
        let sector = bio.bi_sector() as usize;

        for iter in bio.iter() {
            let len = iter.len();
            let offset = iter.offset();

            if rw == block::ReqOp::Read {
                let mut buf = vec![0u8; len];
                disk.read(sector + offset / SECTOR_SIZE, &mut buf)?;
                // 写入 bio
                bio.fill_buffer(&buf)?;
            } else {
                // 从 bio 读取数据
                let buf = bio.read_buffer(len)?;
                disk.write(sector + offset / SECTOR_SIZE, &buf)?;
            }
        }

        bio.bi_status = block::BlkStatus::Ok;
        Ok(())
    }

    fn getgeo(_disk: &Self::Data, geo: &mut block::Geo) -> Result {
        geo.heads = 16;
        geo.sectors = 63;
        geo.cylinders = NUM_SECTORS / (16 * 63);
        geo.start = 0;
        Ok(())
    }
}

struct RustRamDisk {
    _disk: Pin<Box<BlockDeviceHolder>>,
}

impl kernel::Module for RustRamDisk {
    fn init(_module: &'static ThisModule) -> Result<Self> {
        pr_info!("RustRamDisk: initializing\n");

        let disk = Arc::new(RamDisk::new()?);

        let holder = BlockDeviceHolder::register(
            kernel::c_str!("rust_ram"),
            disk,
            SECTOR_SIZE as u32,
            NUM_SECTORS as u64,
        )?;

        pr_info!("RustRamDisk: registered /dev/rust_ram\n");

        Ok(RustRamDisk { _disk: holder })
    }
}
```

## 网络子系统

### 网络设备驱动

```rust
//! Rust 网络设备驱动示例

use kernel::prelude::*;
use kernel::net::{self, Device, DeviceOperations, Packet, PacketType};
use kernel::sync::{Arc, Mutex, SpinLock};

module! {
    type: RustNetDev,
    name: b"rust_netdev",
    author: b"Your Name",
    description: b"Rust network device driver",
    license: b"GPL",
}

struct NetDevData {
    rx_queue: Mutex<Vec<Packet>>,
    tx_count: AtomicU64,
    rx_count: AtomicU64,
}

struct RustNetDevice {
    data: Arc<NetDevData>,
    netdev: Pin<Box<net::Device>>,
}

#[vtable]
impl DeviceOperations for RustNetDevice {
    type Data = Arc<NetDevData>;

    fn open(_data: &Self::Data) -> Result {
        pr_info!("RustNetDevice: open\n");
        Ok(())
    }

    fn stop(_data: &Self::Data) {
        pr_info!("RustNetDevice: stop\n");
    }

    fn start_xmit(data: &Self::Data, packet: Packet) -> net::TxStatus {
        // 模拟发送
        data.tx_count.fetch_add(1, Ordering::Relaxed);

        // 在这里实际发送数据到硬件
        pr_info!("Transmitting packet of {} bytes\n", packet.len());

        net::TxStatus::Ok
    }

    fn get_stats64(data: &Self::Data, stats: &mut net::Stats64) {
        stats.tx_packets = data.tx_count.load(Ordering::Relaxed);
        stats.rx_packets = data.rx_count.load(Ordering::Relaxed);
    }
}

impl kernel::Module for RustNetDev {
    fn init(_module: &'static ThisModule) -> Result<Self> {
        pr_info!("RustNetDev: initializing\n");

        let data = Arc::new(NetDevData {
            rx_queue: Mutex::new(Vec::new()),
            tx_count: AtomicU64::new(0),
            rx_count: AtomicU64::new(0),
        });

        let netdev = net::Device::alloc(kernel::c_str!("rust%d"),
            |netdev| {
                netdev.set_ops(&RustNetDevice);
                netdev.set_mtu(1500);
                netdev.set_flags(net::IFF_NO_PI);
                Ok(())
            })?;

        netdev.register()?;

        pr_info!("RustNetDev: registered {}\n", netdev.name());

        Ok(RustNetDev { data, netdev })
    }
}

impl Drop for RustNetDev {
    fn drop(&mut self) {
        pr_info!("RustNetDev: cleanup\n");
    }
}
```

## eBPF 开发

### Aya 框架入门

**安装工具链：**

```bash
# 安装 Rust eBPF 工具链
cargo install bpf-linker
cargo install cargo-generate

# 生成项目模板
cargo generate --name my-ebpf https://github.com/aya-rs/aya-template
cd my-ebpf
```

### XDP 程序

**eBPF 程序 (my-ebpf-ebpf/src/main.rs):**

```rust
#![no_std]
#![no_main]

use aya_ebpf::{bindings::xdp_action, macros::xdp, programs::XdpContext};
use aya_ebpf::bindings::ethhdr;
use aya_ebpf::helpers::bpf_probe_read_kernel;
use aya_log_ebpf::info;

#[xdp]
pub fn my_xdp_filter(ctx: XdpContext) -> u32 {
    match try_my_xdp_filter(ctx) {
        Ok(ret) => ret,
        Err(_) => xdp_action::XDP_ABORTED,
    }
}

fn try_my_xdp_filter(ctx: XdpContext) -> Result<u32, u32> {
    info!(&ctx, "received a packet");

    // 解析以太网头部
    let ethhdr: *const ethhdr = unsafe { ctx.data() as *const ethhdr };
    if (ethhdr as usize + core::mem::size_of::<ethhdr>()) > ctx.data_end() {
        return Err(xdp_action::XDP_ABORTED);
    }

    let eth_type = unsafe { (*ethhdr).h_proto };

    // 只允许 IPv4 和 IPv6
    match u16::from_be(eth_type) {
        0x0800 => { // IPv4
            info!(&ctx, "IPv4 packet");
            Ok(xdp_action::XDP_PASS)
        }
        0x86DD => { // IPv6
            info!(&ctx, "IPv6 packet");
            Ok(xdp_action::XDP_PASS)
        }
        _ => {
            info!(&ctx, "dropping non-IP packet");
            Ok(xdp_action::XDP_DROP)
        }
    }
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    unsafe { core::hint::unreachable_unchecked() }
}
```

**用户空间程序 (my-ebpf/src/main.rs):**

```rust
use aya::{include_bytes_aligned, Ebpf};
use aya::programs::{Xdp, XdpFlags};
use aya_log::EbpfLogger;
use clap::Parser;
use log::{info, warn};
use tokio::signal;

#[derive(Debug, Parser)]
struct Args {
    #[clap(short, long, default_value = "eth0")]
    iface: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    env_logger::init();

    // 加载 eBPF 程序
    #[cfg(debug_assertions)]
    let mut bpf = Ebpf::load(include_bytes_aligned!(
        "../../target/bpfel-unknown-none/debug/my-ebpf"
    ))?;

    #[cfg(not(debug_assertions))]
    let mut bpf = Ebpf::load(include_bytes_aligned!(
        "../../target/bpfel-unknown-none/release/my-ebpf"
    ))?;

    // 初始化日志
    if let Err(e) = EbpfLogger::init(&mut bpf) {
        warn!("failed to initialize eBPF logger: {}", e);
    }

    // 附加 XDP 程序到网络接口
    let program: &mut Xdp = bpf.program_mut("my_xdp_filter").unwrap().try_into()?;
    program.load()?;
    program.attach(&args.iface, XdpFlags::default())?;

    info!("Waiting for Ctrl-C...");
    signal::ctrl_c().await?;
    info!("Exiting...");

    Ok(())
}
```

### Kprobe 跟踪

```rust
#![no_std]
#![no_main]

use aya_ebpf::{macros::kprobe, programs::ProbeContext};
use aya_log_ebpf::info;

#[kprobe]
pub fn trace_openat(ctx: ProbeContext) -> u32 {
    match try_trace_openat(ctx) {
        Ok(ret) => ret,
        Err(ret) => ret,
    }
}

fn try_trace_openat(ctx: ProbeContext) -> Result<u32, u32> {
    // 读取系统调用参数
    let dfd: i32 = unsafe { ctx.arg(0).ok_or(1u32)? };
    let filename: *const u8 = unsafe { ctx.arg(1).ok_or(1u32)? };

    info!(&ctx, "openat called: dfd={}, filename={:x}", dfd, filename as usize);

    Ok(0)
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    unsafe { core::hint::unreachable_unchecked() }
}
```

### 使用 eBPF 映射

```rust
#![no_std]
#![no_main]

use aya_ebpf::{
    bindings::xdp_action,
    macros::{map, xdp},
    maps::HashMap,
    programs::XdpContext,
};
use aya_log_ebpf::info;
use core::net::Ipv4Addr;

// 定义 eBPF 映射
#[map]
static BLOCKLIST: HashMap<u32, u8> = HashMap::with_max_entries(1024, 0);

#[map]
static PACKET_COUNT: HashMap<u32, u64> = HashMap::with_max_entries(1, 0);

#[xdp]
pub fn xdp_firewall(ctx: XdpContext) -> u32 {
    match try_xdp_firewall(ctx) {
        Ok(ret) => ret,
        Err(_) => xdp_action::XDP_ABORTED,
    }
}

fn try_xdp_firewall(ctx: XdpContext) -> Result<u32, ()> {
    // 解析 IP 头部（简化）
    let ethhdr_len = 14;
    let ip_hdr: *const u8 = unsafe { (ctx.data() as usize + ethhdr_len) as *const u8 };

    if (ip_hdr as usize + 20) > ctx.data_end() {
        return Ok(xdp_action::XDP_PASS);
    }

    // 读取源 IP
    let src_ip = unsafe {
        core::ptr::read_unaligned(ip_hdr.add(12) as *const u32)
    };

    // 检查黑名单
    if unsafe { BLOCKLIST.get(&src_ip).is_some() } {
        info!(&ctx, "Blocked packet from {:i}", Ipv4Addr::from(src_ip));
        return Ok(xdp_action::XDP_DROP);
    }

    // 更新计数器
    let key = 0u32;
    if let Some(count) = unsafe { PACKET_COUNT.get(&key) } {
        let new_count = count.wrapping_add(1);
        unsafe { PACKET_COUNT.insert(&key, &new_count, 0) };
    } else {
        unsafe { PACKET_COUNT.insert(&key, &1u64, 0) };
    }

    info!(&ctx, "Allowed packet from {:i}", Ipv4Addr::from(src_ip));
    Ok(xdp_action::XDP_PASS)
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    unsafe { core::hint::unreachable_unchecked() }
}
```

### TC (流量控制) 程序

```rust
#![no_std]
#![no_main]

use aya_ebpf::{
    macros::{classifier, map},
    maps::Array,
    programs::TcContext,
    bindings::TC_ACT_OK,
};
use aya_log_ebpf::info;

// 带宽限制配置 (kbps)
#[map]
static BANDWIDTH_LIMIT: Array<u64> = Array::with_max_entries(1, 0);

#[classifier]
pub fn tc_bandwidth(ctx: TcContext) -> i32 {
    match try_tc_bandwidth(ctx) {
        Ok(ret) => ret,
        Err(_) => TC_ACT_OK,
    }
}

fn try_tc_bandwidth(ctx: TcContext) -> Result<i32, ()> {
    let pkt_len = ctx.len() as u64 * 8; // 转换为比特

    let limit = unsafe {
        BANDWIDTH_LIMIT.get(0).copied().unwrap_or(1_000_000) // 默认 1 Gbps
    };

    // 简单的令牌桶算法
    // 注意：实际实现需要更复杂的逻辑和状态存储

    if pkt_len > limit {
        info!(&ctx, "Dropping packet: {} bits exceeds limit {} kbps",
              pkt_len, limit);
        return Ok(TC_ACT_SHOT); // 丢弃数据包
    }

    Ok(TC_ACT_OK)
}

const TC_ACT_SHOT: i32 = 2;

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    unsafe { core::hint::unreachable_unchecked() }
}
```

## 调试和测试

### 内核调试

```bash
# 查看内核日志
sudo dmesg | grep -i rust

# 实时监控
sudo dmesg -w

# 加载模块
sudo insmod rust_hello.ko

# 卸载模块
sudo rmmod rust_hello

# 查看模块信息
modinfo rust_hello.ko
```

### 使用 GDB

```bash
# 调试内核模块
# 在 QEMU 中运行内核
gdb vmlinux

# 在 GDB 中
(gdb) target remote :1234
(gdb) break rust_hello_init
(gdb) continue
```

### eBPF 调试

```bash
# 查看 eBPF 程序
sudo bpftool prog list

# 查看 eBPF 映射
sudo bpftool map list

# 查看映射内容
sudo bpftool map dump name BLOCKLIST

# 查看 eBPF 日志
sudo cat /sys/kernel/debug/tracing/trace_pipe
```

---

Rust for Linux 为内核开发带来了新的可能性。关键要点：

1. **安全第一**：利用 Rust 的类型系统防止常见漏洞
2. **渐进采用**：从非关键驱动开始逐步引入 Rust
3. **社区参与**：关注 Rust-for-Linux 邮件列表和补丁
4. **测试充分**：使用内核测试框架和 CI/CD
5. **文档完整**：遵循内核文档规范

随着项目的成熟，Rust 将成为 Linux 内核开发的重要组成部分。
