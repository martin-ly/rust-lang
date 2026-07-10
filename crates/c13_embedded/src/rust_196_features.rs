//! Rust 1.96.0 嵌入式相关稳定特性实现模块
//! **历史稳定 patch**: Rust 1.96.1（基于 Rust 1.96.0 特性集）
//! Rust 1.96.0/1.96.1 feature module
//! 所有公共 API 均使用 `core` 类型，保持 `no_std` 兼容性：
//! all API `core` type ， `no_std` ：
//! 所有公共 API 均Use `core` type，保持 `no_std` 兼容性：
//! all API Use `core` type， `no_std` ：
//! - `core::assert_matches!` — 嵌入式状态机测试
//! # 版本信息
//! # this
//! - Rust 版本: 1.96.0+ / nightly 1.98
//! - Rust 版this: 1.96.0+ / nightly 1.98
//! - 稳定日期: 2026-05-28
//! - date : 2026-05-28
//! - 稳定date: 2026-05-28
//! - date: 2026-05-28
//! # 安全说明
//! # explain
//! # 安全explain
//! 本模块**完全禁止 unsafe 代码**，所有示例均在 safe Rust 中实现。
//! this module ** unsafe **，all example in safe Rust in 。

#![forbid(unsafe_code)]

// ============================================================================
// 1. core::range — no_std 友好的寄存器地址范围与内存映射迭代
// ============================================================================

/// 内存区域描述符，使用 `core::range::Range` 表示半开地址区间。
/// memory area describe ， `core::range::Range` represent interval 。
/// `core::range::Range` 实现 `Copy`，可以在中断上下文之间自由传递，
/// `core::range::Range` `Copy`，can in in on under 's ，
/// 无需担心所有权或生命周期问题。
/// ownership or lifetime problem 。
/// 无需担心ownershiporlifetimeproblem。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemoryRegion {
    /// 区域名称（静态字符串，no_std 安全）
    /// area （，no_std ）
    pub name: &'static str,
    /// 地址range `[start, end)`，Use `core::range::Range` 公共field
    pub range: core::range::Range<usize>,
    /// 访问权限标志
    /// mark
    pub flags: RegionFlags,
}

/// 区域访问权限标志。
/// area mark 。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RegionFlags {
    pub readable: bool,
    pub writable: bool,
    pub executable: bool,
}

pub struct MemoryMap {
    regions: [MemoryRegion; 4],
}

impl MemoryMap {
    /// 构造一个典型的嵌入式系统内存映射示例。
    /// system memory mapping example 。
    /// 使用 `core::range::Range { start, end }` 直接构造地址范围。
    /// Use `core::range::Range { start, end }` 直接构造地址range。
    pub const fn example_map() -> Self {
        Self {
            regions: [
                MemoryRegion {
                    name: "FLASH",
                    range: core::range::Range {
                        start: 0x0800_0000,
                        end: 0x0801_0000,
                    },
                    flags: RegionFlags {
                        readable: true,
                        writable: false,
                        executable: true,
                    },
                },
                MemoryRegion {
                    name: "SRAM",
                    range: core::range::Range {
                        start: 0x2000_0000,
                        end: 0x2000_8000,
                    },
                    flags: RegionFlags {
                        readable: true,
                        writable: true,
                        executable: false,
                    },
                },
                MemoryRegion {
                    name: "PERIPHERAL",
                    range: core::range::Range {
                        start: 0x4000_0000,
                        end: 0x4002_0000,
                    },
                    flags: RegionFlags {
                        readable: true,
                        writable: true,
                        executable: false,
                    },
                },
                MemoryRegion {
                    name: "MMIO_RESERVED",
                    range: core::range::Range {
                        start: 0xE000_0000,
                        end: 0xE010_0000,
                    },
                    flags: RegionFlags {
                        readable: true,
                        writable: false,
                        executable: false,
                    },
                },
            ],
        }
    }

    /// 查找包含给定地址的内存区域。
    /// memory area 。
    pub fn region_containing(&self, addr: usize) -> Option<&MemoryRegion> {
        self.regions
            .iter()
            .find(|r| addr >= r.range.start && addr < r.range.end)
    }

    /// 返回所有区域。
    /// all area 。
    pub const fn regions(&self) -> &[MemoryRegion; 4] {
        &self.regions
    }

    /// 计算所有区域的总字节数。
    /// all area 。
    pub fn total_size(&self) -> usize {
        let mut sum = 0usize;
        let mut i = 0;
        while i < self.regions.len() {
            sum += self.regions[i].range.end - self.regions[i].range.start;
            i += 1;
        }
        sum
    }
}

/// 寄存器块迭代器，使用 `core::range::Range` 步进遍历寄存器偏移。
/// ， `core::range::Range` 。
pub struct RegisterBlockIter {
    offset_range: core::range::Range<usize>,
    step: usize,
}

impl RegisterBlockIter {
    /// 创建一个新的寄存器块迭代器。
    /// 。
    pub const fn new(start_offset: usize, end_offset: usize, step: usize) -> Self {
        Self {
            offset_range: core::range::Range {
                start: start_offset,
                end: end_offset,
            },
            step,
        }
    }

    /// 获取下一个寄存器偏移（若仍在范围内）。
    /// under （in scope inside ）。
    pub fn next_offset(&mut self) -> Option<usize> {
        if self.offset_range.start < self.offset_range.end {
            let current = self.offset_range.start;
            self.offset_range.start += self.step;
            Some(current)
        } else {
            None
        }
    }
}

// ============================================================================
// 2. ManuallyDrop 模式 — 硬件寄存器标签，避免 Drop 副作用
// ============================================================================

/// 在嵌入式系统中，某些值代表外设寄存器状态或 DMA 描述符，
/// in system in ，outside state or DMA describe ，
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HardwareRegisterTag<T: Copy> {
    pub raw: core::mem::ManuallyDrop<T>,
    /// 寄存器地址偏移（用于调试/日志）
    /// （/）
    pub offset: u16,
}

impl<T: Copy> HardwareRegisterTag<T> {
    /// 从原始值构造寄存器标签（无 Drop 副作用）。
    /// from （ Drop role ）。
    pub const fn new(raw: T, offset: u16) -> Self {
        Self {
            raw: core::mem::ManuallyDrop::new(raw),
            offset,
        }
    }

    pub fn value(&self) -> T {
        // ManuallyDrop<T> 在 T: Copy 时实现 Copy，可直接复制后解构
        let copied = self.raw;
        core::mem::ManuallyDrop::into_inner(copied)
    }
}

/// DMA 描述符标签示例。
/// DMA describe example 。
/// DMA 描述符通常包含物理地址和控制字，
/// DMA describe and ，
/// 我们绝不希望在作用域结束时自动释放这些资源。
/// in role domain end 。
/// in role domain 。
pub type DmaDescriptorTag = HardwareRegisterTag<u32>;

/// GPIO 状态标签示例。
/// GPIO state example 。
pub type GpioStatusTag = HardwareRegisterTag<u16>;

// ============================================================================
// 3. assert_matches! — 嵌入式状态机测试
// ============================================================================

/// 嵌入式设备状态机。
/// state machine 。
/// 嵌入式设备state machine。
/// 典型的低功耗设备状态转换：
/// low state conversion ：
/// state conversion ：
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeviceState {
    Boot,
    Init { step: u8 },
    Idle,
    Active { peripheral_mask: u32 },
    Sleep { wake_source: WakeSource },
    Error { code: u16 },
}

/// 唤醒源。
/// 。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WakeSource {
    Timer,
    Gpio { pin: u8 },
    Uart,
    Unknown,
}

/// 使用 `core::assert_matches!` 验证状态机转换。
/// `core::assert_matches!` state machine conversion 。
/// 相比 `assert!(matches!(...))`，失败时打印 `Debug` 表示，
/// `assert!(matches!(...))`，failure `Debug` represent ，
/// `assert!(matches!(...))`， `Debug` represent ，
/// 相比 `assert!(matches!(...))`，失败时Print `Debug` represent，
/// 在资源受限的嵌入式调试环境中尤为宝贵。
/// in environment in as 。
pub fn verify_state_transition(
    old_state: DeviceState,
    new_state: DeviceState,
) -> Result<(), &'static str> {
    use core::assert_matches;

    // 验证旧状态必须是可转换的状态之一
    assert_matches!(
        old_state,
        DeviceState::Boot
            | DeviceState::Init { .. }
            | DeviceState::Idle
            | DeviceState::Active { .. }
            | DeviceState::Sleep { .. }
    );

    // 验证新状态必须是合法的目标状态
    assert_matches!(
        new_state,
        DeviceState::Init { .. }
            | DeviceState::Idle
            | DeviceState::Active { .. }
            | DeviceState::Sleep { .. }
            | DeviceState::Error { .. }
    );

    // 简化的状态转换规则检查
    match (old_state, new_state) {
        (DeviceState::Boot, DeviceState::Init { .. }) => Ok(()),
        (DeviceState::Init { .. }, DeviceState::Idle) => Ok(()),
        (DeviceState::Idle, DeviceState::Active { .. }) => Ok(()),
        (DeviceState::Idle, DeviceState::Sleep { .. }) => Ok(()),
        (DeviceState::Active { .. }, DeviceState::Idle) => Ok(()),
        (DeviceState::Sleep { .. }, DeviceState::Idle) => Ok(()),
        (_, DeviceState::Error { .. }) => Ok(()),
        _ => Err("invalid_state_transition"),
    }
}

// ============================================================================
// 演示函数
// ============================================================================

/// 运行 Rust 1.96 嵌入式特性演示
/// Run Rust 1.96 feature demonstration
#[cfg(not(target_arch = "arm"))]
pub fn demonstrate_rust_196_features() {
    use core::assert_matches;

    println!("\n========================================");
    println!("   Rust 1.96.0 嵌入式特性演示");
    println!("========================================\n");

    // core::range::Range 演示
    let mem_map = MemoryMap::example_map();
    println!("内存映射总大小: {} bytes", mem_map.total_size());

    let flash = mem_map.region_containing(0x0800_1000);
    assert_matches!(flash, Some(_));
    println!("FLASH 区域: {:?}", flash.unwrap().range);

    // core::range::RangeInclusive 演示
    let ri = core::range::RangeInclusive {
        start: 0x1000,
        last: 0x1FFF,
    };
    println!(
        "寄存器包含范围: {:?} ({} registers)",
        ri,
        ri.last - ri.start + 1
    );

    // ManuallyDrop 演示
    let dma_tag = DmaDescriptorTag::new(0x2000_0000, 0x0400);
    println!(
        "DMA 描述符: value={:#010x}, offset={:#06x}",
        dma_tag.value(),
        dma_tag.offset
    );

    // assert_matches! 演示
    let state = DeviceState::Init { step: 2 };
    assert_matches!(state, DeviceState::Init { step: 2 });
    println!("状态机验证通过: {:?}", state);

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取特性信息
/// feature
pub fn get_rust_196_embedded_info() -> &'static str {
    "Rust 1.96.0 嵌入式特性:\n- core::range::Range { start, end } — no_std 友好的内存范围\n- \
     core::range::RangeInclusive { start, last } — 包含性寄存器范围\n- core::mem::ManuallyDrop — \
     硬件寄存器标签，控制析构\n- core::assert_matches! — 嵌入式状态机模式断言"
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use core::assert_matches;

    #[test]
    fn test_memory_region_copy_semantics() {
        let region = MemoryRegion {
            name: "TEST",
            range: core::range::Range {
                start: 0x1000,
                end: 0x2000,
            },
            flags: RegionFlags {
                readable: true,
                writable: false,
                executable: false,
            },
        };
        let copied = region; // Copy
        assert_eq!(region.range.start, copied.range.start);
        assert_eq!(region.range.end, copied.range.end);
    }

    #[test]
    fn test_memory_map_region_containing() {
        let map = MemoryMap::example_map();

        let flash = map.region_containing(0x0800_0000);
        assert_matches!(flash, Some(r) if r.name == "FLASH");

        let sram = map.region_containing(0x2000_4000);
        assert_matches!(sram, Some(r) if r.name == "SRAM");

        let none = map.region_containing(0x0000_0000);
        assert_matches!(none, None);
    }

    #[test]
    fn test_memory_map_total_size() {
        let map = MemoryMap::example_map();
        let expected = 0x1_0000 + 0x8000 + 0x2_0000 + 0x10_0000;
        assert_eq!(map.total_size(), expected);
    }

    #[test]
    fn test_register_block_iter() {
        let mut iter = RegisterBlockIter::new(0x00, 0x20, 0x04);
        assert_eq!(iter.next_offset(), Some(0x00));
        assert_eq!(iter.next_offset(), Some(0x04));
        assert_eq!(iter.next_offset(), Some(0x08));
        assert_eq!(iter.next_offset(), Some(0x0C));
        assert_eq!(iter.next_offset(), Some(0x10));
        assert_eq!(iter.next_offset(), Some(0x14));
        assert_eq!(iter.next_offset(), Some(0x18));
        assert_eq!(iter.next_offset(), Some(0x1C));
        assert_eq!(iter.next_offset(), None);
    }

    #[test]
    fn test_hardware_register_tag() {
        let tag = HardwareRegisterTag::new(0xDEADBEEFu32, 0x400);
        assert_eq!(tag.value(), 0xDEADBEEF);
        assert_eq!(tag.offset, 0x400);

        // ManuallyDrop 不会自动调用 Drop
        let copied = tag;
        assert_eq!(copied.value(), 0xDEADBEEF);
    }

    #[test]
    fn test_dma_descriptor_tag() {
        let dma = DmaDescriptorTag::new(0x2000_0000, 0x0400);
        assert_eq!(dma.value(), 0x2000_0000);
    }

    #[test]
    fn test_gpio_status_tag() {
        let gpio = GpioStatusTag::new(0b0000_0001_0010_1100, 0x0010);
        assert_eq!(gpio.value(), 0b0000_0001_0010_1100);
    }

    #[test]
    fn test_assert_matches_device_state() {
        let boot = DeviceState::Boot;
        assert_matches!(boot, DeviceState::Boot);

        let init = DeviceState::Init { step: 3 };
        assert_matches!(init, DeviceState::Init { step: 3 });

        let active = DeviceState::Active {
            peripheral_mask: 0x0F,
        };
        assert_matches!(
            active,
            DeviceState::Active {
                peripheral_mask: 0x0F
            }
        );

        let sleep = DeviceState::Sleep {
            wake_source: WakeSource::Gpio { pin: 5 },
        };
        assert_matches!(
            sleep,
            DeviceState::Sleep {
                wake_source: WakeSource::Gpio { pin: 5 }
            }
        );
    }

    #[test]
    fn test_state_transition_valid() {
        assert!(verify_state_transition(DeviceState::Boot, DeviceState::Init { step: 0 }).is_ok());
        assert!(verify_state_transition(DeviceState::Init { step: 3 }, DeviceState::Idle).is_ok());
        assert!(
            verify_state_transition(
                DeviceState::Idle,
                DeviceState::Active { peripheral_mask: 1 }
            )
            .is_ok()
        );
        assert!(
            verify_state_transition(
                DeviceState::Idle,
                DeviceState::Sleep {
                    wake_source: WakeSource::Timer
                }
            )
            .is_ok()
        );
    }

    #[test]
    fn test_state_transition_invalid() {
        assert!(
            verify_state_transition(
                DeviceState::Boot,
                DeviceState::Idle // 跳过 Init
            )
            .is_err()
        );
        assert!(
            verify_state_transition(
                DeviceState::Sleep {
                    wake_source: WakeSource::Timer
                },
                DeviceState::Active { peripheral_mask: 1 } // 必须先回到 Idle
            )
            .is_err()
        );
    }

    #[test]
    fn test_core_range_into_iter() {
        let r = core::range::Range { start: 0, end: 5 };
        let mut sum = 0u32;
        for i in r {
            sum += i as u32;
        }
        assert_eq!(sum, 10);
    }

    #[test]
    fn test_range_inclusive_fields() {
        let ri = core::range::RangeInclusive {
            start: 10,
            last: 15,
        };
        assert_eq!(ri.start, 10);
        assert_eq!(ri.last, 15);

        let mut count = 0u32;
        for _i in ri {
            count += 1;
        }
        assert_eq!(count, 6); // 10, 11, 12, 13, 14, 15
    }

    #[test]
    fn test_get_rust_196_embedded_info() {
        let info = get_rust_196_embedded_info();
        assert!(info.contains("core::range::Range"));
        assert!(info.contains("ManuallyDrop"));
        assert!(info.contains("assert_matches"));
    }
}
