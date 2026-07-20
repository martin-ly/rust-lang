// FFI 跨语言互操作示例 FFI Example
#[repr(C)]
pub struct MyStruct {
    pub a: i32,
    pub b: f64,
}

extern "C" {
    fn c_func(x: i32) -> i32;
}

fn main() {
    unsafe {
        // 假设已链接C库
        // let result = c_func(42);
        // println!("C func result: {}", result);
    }
} 