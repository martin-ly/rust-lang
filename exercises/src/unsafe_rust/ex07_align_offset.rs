//! # 练习 7: 内存对齐与未对齐访问
//!
//! **难度**: Hard  
//! **考点**: `align_of`、`align_to`、未对齐读取（`read_unaligned`）、`packed` struct
//!
//! ## 题目描述
//!
//! Rust 要求所有类型都满足对齐（alignment）约束。
//! 违反对齐约束的内存访问是 **Undefined Behavior (UB)**。
//!
//! 然而，在解析二进制协议、网络包或文件格式时，
//! 数据往往不会按 Rust 的对齐要求排布。
//! 本练习学习如何在这些场景下**安全地**处理未对齐数据。
//!
//! ## 要求
//!
//! - 使用 `read_unaligned` / `write_unaligned` 读取未对齐的整数
//! - 理解 `#[repr(packed)]` 对结构体字段对齐的影响
//! - 使用 `ptr::align_offset` 计算指针到下一个对齐地址的偏移

/// 从未对齐的字节缓冲区读取一个 `u32`（小端序）
///
/// # Safety
///
/// 调用者必须确保 `bytes` 至少有 4 个字节。
/// 本函数内部使用 `read_unaligned`，因此不需要 `bytes` 按 `u32` 对齐。
pub unsafe fn read_u32_le_unaligned(bytes: *const u8) -> u32 {
    // SAFETY: 调用者保证 bytes 指向至少 4 字节的有效内存。
    // read_unaligned 不要求指针对齐。
    let val = unsafe { std::ptr::read_unaligned(bytes as *const u32) };
    // 如果目标是小端序，直接使用；如果是大端序，需要交换字节序。
    // 为了确定性，我们总是先按小端序解释，然后根据主机字节序调整。
    u32::from_le(val)
}

/// 将 `u32`（小端序）写入未对齐的字节缓冲区
///
/// # Safety
///
/// 调用者必须确保 `bytes` 指向至少 4 字节的可写内存。
pub unsafe fn write_u32_le_unaligned(bytes: *mut u8, value: u32) {
    // SAFETY: 调用者保证 bytes 指向至少 4 字节的有效可写内存。
    let le_value = value.to_le();
    unsafe { std::ptr::write_unaligned(bytes as *mut u32, le_value) };
}

/// 一个模拟网络包头的 packed 结构体
///
/// `#[repr(C, packed)]` 表示：
/// - 字段按 C 语言顺序排列
/// - 无填充字节（packed），字段之间不插入对齐填充
///
/// ⚠️ **警告**: 对 packed struct 的字段取引用是 unsafe 的，
/// 因为字段可能未对齐。
#[repr(C, packed)]
#[derive(Debug, Copy, Clone)]
pub struct NetworkPacketHeader {
    pub flags: u8,
    pub length: u16,
    pub seq: u32,
}

/// 将 packed struct 的字段按小端序序列化为字节数组
///
/// 由于 struct 是 packed 的，我们可以直接将其内存按字节复制，
/// 但这里我们手动序列化以练习未对齐写入。
pub fn serialize_packet_header(header: &NetworkPacketHeader) -> [u8; 7] {
    let mut buf = [0u8; 7];

    // SAFETY: NetworkPacketHeader 是 packed 的，字段可能未对齐。
    // 我们不能直接对字段取引用（`&header.length` 是 unsafe 的）。
    // 使用 `std::ptr::addr_of!` 获取字段的原始指针，然后用 read_unaligned。
    unsafe {
        buf[0] = std::ptr::addr_of!(header.flags).read();
        let length_ptr = std::ptr::addr_of!(header.length);
        let length_val = std::ptr::read_unaligned(length_ptr);
        buf[1..3].copy_from_slice(&length_val.to_le_bytes());

        let seq_ptr = std::ptr::addr_of!(header.seq);
        let seq_val = std::ptr::read_unaligned(seq_ptr);
        buf[3..7].copy_from_slice(&seq_val.to_le_bytes());
    }

    buf
}

/// 从字节数组反序列化为 packed struct
///
/// # Safety
///
/// `buf` 必须至少有 7 个字节。
pub unsafe fn deserialize_packet_header(buf: *const u8) -> NetworkPacketHeader {
    // SAFETY: 调用者保证 buf 指向至少 7 字节的有效内存。
    unsafe {
        NetworkPacketHeader {
            flags: buf.read(),
            length: std::ptr::read_unaligned(buf.add(1) as *const u16).to_le(),
            seq: std::ptr::read_unaligned(buf.add(3) as *const u32).to_le(),
        }
    }
}

/// 计算将指针提升到下一个 `align` 对齐地址所需的偏移量
///
/// 如果指针已经对齐，返回 0。
///
/// # Examples
///
/// ```
/// use exercises::unsafe_rust::ex07_align_offset::padding_to_align;
/// assert_eq!(padding_to_align(1, 4), 3); // 1 -> 需要 3 字节到 4
/// assert_eq!(padding_to_align(4, 4), 0); // 已经对齐
/// assert_eq!(padding_to_align(5, 4), 3); // 5 -> 需要 3 字节到 8
/// ```
pub fn padding_to_align(addr: usize, align: usize) -> usize {
    assert!(align.is_power_of_two(), "align 必须是 2 的幂");
    let mask = align - 1;
    if addr & mask == 0 {
        0
    } else {
        align - (addr & mask)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read_write_u32_unaligned() {
        // 使用一个未按 u32 对齐的缓冲区
        let mut buf = [0u8; 8];
        // 从偏移 1 开始写入，这是未对齐的
        unsafe {
            write_u32_le_unaligned(buf.as_mut_ptr().add(1), 0x12345678);
            let val = read_u32_le_unaligned(buf.as_ptr().add(1));
            assert_eq!(val, 0x12345678);
        }
    }

    #[test]
    fn test_serialize_deserialize_packet() {
        let header = NetworkPacketHeader {
            flags: 0xAB,
            length: 0x1234,
            seq: 0xDEADBEEF,
        };

        let serialized = serialize_packet_header(&header);
        assert_eq!(serialized[0], 0xAB);
        assert_eq!(&serialized[1..3], &[0x34, 0x12]); // 小端序
        assert_eq!(&serialized[3..7], &[0xEF, 0xBE, 0xAD, 0xDE]); // 小端序

        unsafe {
            let deserialized = deserialize_packet_header(serialized.as_ptr());
            // 对 #[repr(packed)] struct 的字段直接取引用是 UB，
            // 需要先将字段值复制到局部变量。
            let deserialized_flags = { deserialized.flags };
            let deserialized_length = { deserialized.length };
            let deserialized_seq = { deserialized.seq };
            let header_flags = { header.flags };
            let header_length = { header.length };
            let header_seq = { header.seq };
            assert_eq!(deserialized_flags, header_flags);
            assert_eq!(deserialized_length, header_length);
            assert_eq!(deserialized_seq, header_seq);
        }
    }

    #[test]
    fn test_padding_to_align() {
        assert_eq!(padding_to_align(0, 1), 0);
        assert_eq!(padding_to_align(0, 4), 0);
        assert_eq!(padding_to_align(1, 4), 3);
        assert_eq!(padding_to_align(2, 4), 2);
        assert_eq!(padding_to_align(3, 4), 1);
        assert_eq!(padding_to_align(4, 4), 0);
        assert_eq!(padding_to_align(5, 4), 3);
        assert_eq!(padding_to_align(7, 8), 1);
        assert_eq!(padding_to_align(8, 8), 0);
        assert_eq!(padding_to_align(9, 8), 7);
    }

    #[test]
    #[should_panic(expected = "align 必须是 2 的幂")]
    fn test_padding_to_align_non_power_of_two() {
        padding_to_align(1, 3);
    }
}
