use std::ptr::NonNull;

fn main() {
    let mut v = vec![1, 2, 3];
    let p = NonNull::new(v.as_mut_ptr()).unwrap();
    unsafe {
        // 在长度范围内写入
        *p.as_ptr() = 9;
    }
    println!("v={:?}", v);
}


