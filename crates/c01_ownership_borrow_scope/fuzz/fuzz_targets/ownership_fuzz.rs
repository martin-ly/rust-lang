#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // 测试所有权和借用处理任意输入
    if data.len() > 0 {
        let vec: Vec<u8> = data.to_vec();
        let borrowed = &vec;
        assert_eq!(borrowed.len(), data.len());
    }
});
