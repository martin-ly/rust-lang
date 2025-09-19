#[repr(packed)]
#[derive(Copy, Clone)]
#[allow(dead_code)]
struct Packed { a: u8, b: u32 }

fn read_b(p: &Packed) -> u32 {
    // 安全读取：使用未对齐读，且避免创建对 packed 字段的引用
    unsafe {
        let ptr = std::ptr::addr_of!((*p).b) as *const u32;
        std::ptr::read_unaligned(ptr)
    }
}

fn main() {
    let p = Packed { a: 1, b: 0x01020304 };
    println!("b=0x{:08x}", read_b(&p));
}


