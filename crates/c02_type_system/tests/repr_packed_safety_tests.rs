#[repr(packed)]
#[derive(Copy, Clone)]
#[allow(dead_code)]
struct Packed { a: u8, b: u32 }

fn read_b(p: &Packed) -> u32 {
    unsafe {
        let ptr = std::ptr::addr_of!((*p).b) as *const u32;
        std::ptr::read_unaligned(ptr)
    }
}

#[test]
fn test_read_b() {
    let p = Packed { a: 0, b: 0x0a0b0c0d };
    assert_eq!(read_b(&p), 0x0a0b0c0d);
}


