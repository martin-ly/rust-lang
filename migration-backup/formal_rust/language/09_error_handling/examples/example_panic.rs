// 错误处理案例：panic与不可恢复错误
// 理论映射：对应“panic”与“不可恢复错误”理论（见 01_formal_error_model.md 附录）

fn main() {
    let v = vec![1, 2, 3];
    // 下面这行会导致panic
    // println!("第4个元素: {}", v[3]);
    println!("程序正常结束");
} 