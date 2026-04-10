// Miri 测试示例文件
// 用于验证 Miri 安装和配置

fn main() {
    println!("Miri 测试示例");
    
    // 测试 1: 基本内存安全
    let x = 42;
    let r = &x;
    assert_eq!(*r, 42);
    println!("✓ 基本内存安全测试通过");
    
    // 测试 2: 安全的 unsafe 代码
    unsafe {
        let mut y = 0;
        let ptr = &mut y as *mut i32;
        *ptr = 100;
        assert_eq!(y, 100);
    }
    println!("✓ 安全 unsafe 代码测试通过");
    
    // 测试 3: MaybeUninit
    use std::mem::MaybeUninit;
    let mut val = MaybeUninit::<i32>::uninit();
    unsafe {
        val.as_mut_ptr().write(42);
        assert_eq!(val.assume_init(), 42);
    }
    println!("✓ MaybeUninit 测试通过");
    
    println!("\n所有测试通过！Miri 配置正确。");
}

#[test]
fn test_basic_safety() {
    let x = 42;
    let r = &x;
    assert_eq!(*r, 42);
}

#[test]
fn test_unsafe_safety() {
    unsafe {
        let mut y = 0;
        let ptr = &mut y as *mut i32;
        *ptr = 100;
        assert_eq!(y, 100);
    }
}
