#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // 测试算法处理任意输入
    if data.len() > 0 {
        let mut vec: Vec<u8> = data.to_vec();
        vec.sort();
        assert_eq!(vec.len(), data.len());
    }
});
