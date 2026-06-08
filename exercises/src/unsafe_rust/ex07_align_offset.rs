//! # 练习 7: 内存对齐与未对齐访问 / Exercise 7: Memory Alignment and Unaligned Access
//!
//! **难度 / Difficulty**: Hard  
//! **考点 / Focus**: `align_of`、`align_to`、未对齐读取（`read_unaligned`）、`packed` struct
//!   `read_unaligned`, `packed` struct
//!
//! ## 题目描述 / Problem Description
//!
//! Rust 要求所有类型都满足对齐（alignment）约束。
//! Rust requires all types to satisfy alignment constraints.
//! 违反对齐约束的内存访问是 **Undefined Behavior (UB)**。
//! Violating alignment constraints is **Undefined Behavior (UB)**.
//!
//! 然而，在解析二进制协议、网络包或文件格式时，
//! However, when parsing binary protocols, network packets, or file formats,
//! 数据往往不会按 Rust 的对齐要求排布。
//! data often isn't laid out according to Rust's alignment requirements.
//! 本练习学习如何在这些场景下**安全地**处理未对齐数据。
//! This exercise learns how to **safely** handle unaligned data in these scenarios.
//!
//! ## 要求 / Requirements
//!
//! - 使用 `read_unaligned` / `write_unaligned` 读取未对齐的整数
//!   Use `read_unaligned` / `write_unaligned` for unaligned integers
//! - 理解 `#[repr(packed)]` 对结构体字段对齐的影响
//!   Understand `#[repr(packed)]` effect on struct field alignment
//! - 使用 `ptr::align_offset` 计算指针到下一个对齐地址的偏移
//!   Use `ptr::align_offset` to compute offset to next aligned address

/// 从未对齐的字节缓冲区读取一个 `u32`（小端序）
/// Reads a `u32` (little-endian) from unaligned byte buffer
///
/// # Safety
///
/// 调用者必须确保 `bytes` 至少有 4 个字节。
/// Caller must ensure `bytes` has at least 4 bytes.
/// 本函数内部使用 `read_unaligned`，因此不需要 `bytes` 按 `u32` 对齐。
/// This function uses `read_unaligned` internally, so `bytes` need not be `u32`-aligned.
pub unsafe fn read_u32_le_unaligned(bytes: *const u8) -> u32 {
    // SAFETY: 调用者保证 bytes 指向至少 4 字节的有效内存。
    // SAFETY: Caller guarantees bytes points to at least 4 bytes of valid memory.
    // read_unaligned 不要求指针对齐。
    // read_unaligned does not require pointer alignment.
    let val = unsafe { std::ptr::read_unaligned(bytes as *const u32) };
    u32::from_le(val)
}

/// 将 `u32`（小端序）写入未对齐的字节缓冲区
/// Writes `u32` (little-endian) to unaligned byte buffer
///
/// # Safety
///
/// 调用者必须确保 `bytes` 指向至少 4 字节的可写内存。
/// Caller must ensure `bytes` points to at least 4 bytes of writable memory.
pub unsafe fn write_u32_le_unaligned(bytes: *mut u8, value: u32) {
    // SAFETY: 调用者保证 bytes 指向至少 4 字节的有效可写内存。
    // SAFETY: Caller guarantees bytes points to at least 4 bytes of valid writable memory.
    let le_value = value.to_le();
    unsafe { std::ptr::write_unaligned(bytes as *mut u32, le_value) };
}

/// 一个模拟网络包头的 packed 结构体
/// A packed struct simulating a network packet header
///
/// `#[repr(C, packed)]` 表示：
/// `#[repr(C, packed)]` means:
/// - 字段按 C 语言顺序排列 / Fields arranged in C order
/// - 无填充字节（packed），字段之间不插入对齐填充
///   No padding bytes (packed), no alignment padding between fields
///
/// ⚠️ **警告 / Warning**: 对 packed struct 的字段取引用是 unsafe 的，
/// Taking references to packed struct fields is unsafe,
/// 因为字段可能未对齐。
/// because fields may be unaligned.
#[repr(C, packed)]
#[derive(Debug, Copy, Clone)]
pub struct NetworkPacketHeader {
    pub flags: u8,
    pub length: u16,
    pub seq: u32,
}

/// 将 packed struct 的字段按小端序序列化为字节数组
/// Serializes packed struct fields to byte array in little-endian
///
/// 由于 struct 是 packed 的，我们可以直接将其内存按字节复制，
/// Since struct is packed, we could directly copy its memory as bytes,
/// 但这里我们手动序列化以练习未对齐写入。
/// but here we manually serialize to practice unaligned writes.
pub fn serialize_packet_header(header: &NetworkPacketHeader) -> [u8; 7] {
    let mut buf = [0u8; 7];

    // SAFETY: NetworkPacketHeader 是 packed 的，字段可能未对齐。
    // SAFETY: NetworkPacketHeader is packed, fields may be unaligned.
    // 我们不能直接对字段取引用（`&header.length` 是 unsafe 的）。
    // We cannot directly reference fields (`&header.length` is unsafe).
    // 使用 `std::ptr::addr_of!` 获取字段的原始指针，然后用 read_unaligned。
    // Use `std::ptr::addr_of!` to get field raw pointers, then read_unaligned.
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
/// Deserializes byte array to packed struct
///
/// # Safety
///
/// `buf` 必须至少有 7 个字节。
/// `buf` must have at least 7 bytes.
pub unsafe fn deserialize_packet_header(buf: *const u8) -> NetworkPacketHeader {
    // SAFETY: 调用者保证 buf 指向至少 7 字节的有效内存。
    // SAFETY: Caller guarantees buf points to at least 7 bytes of valid memory.
    unsafe {
        NetworkPacketHeader {
            flags: buf.read(),
            length: std::ptr::read_unaligned(buf.add(1) as *const u16).to_le(),
            seq: std::ptr::read_unaligned(buf.add(3) as *const u32).to_le(),
        }
    }
}

/// 计算将指针提升到下一个 `align` 对齐地址所需的偏移量
/// Computes offset needed to advance pointer to next `align`-aligned address
///
/// 如果指针已经对齐，返回 0。
/// Returns 0 if pointer is already aligned.
///
/// # Examples
///
/// ```
/// use exercises::unsafe_rust::ex07_align_offset::padding_to_align;
/// assert_eq!(padding_to_align(1, 4), 3); // 1 -> 需要 3 字节到 4 / Need 3 bytes to reach 4
/// assert_eq!(padding_to_align(4, 4), 0); // 已经对齐 / Already aligned
/// assert_eq!(padding_to_align(5, 4), 3); // 5 -> 需要 3 字节到 8 / Need 3 bytes to reach 8
/// ```
pub fn padding_to_align(addr: usize, align: usize) -> usize {
    assert!(
        align.is_power_of_two(),
        "align 必须是 2 的幂 / align must be power of two"
    );
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
        // Use a buffer not aligned to u32
        let mut buf = [0u8; 8];
        // 从偏移 1 开始写入，这是未对齐的
        // Write from offset 1, which is unaligned
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
        assert_eq!(&serialized[1..3], &[0x34, 0x12]); // 小端序 / Little-endian
        assert_eq!(&serialized[3..7], &[0xEF, 0xBE, 0xAD, 0xDE]); // 小端序 / Little-endian

        unsafe {
            let deserialized = deserialize_packet_header(serialized.as_ptr());
            // 对 #[repr(packed)] struct 的字段直接取引用是 UB，
            // Taking direct references to #[repr(packed)] struct fields is UB,
            // 需要先将字段值复制到局部变量。
            // need to copy field values to local variables first.
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
