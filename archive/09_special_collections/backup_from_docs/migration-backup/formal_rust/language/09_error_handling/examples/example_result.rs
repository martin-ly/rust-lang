// 错误处理案例：Result类型与错误传播
// 理论映射：对应“错误类型”与“错误传播一致性”定理（见 01_formal_error_model.md 附录）

fn divide(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err("除数不能为0".to_string())
    } else {
        Ok(a / b)
    }
}

fn main() {
    match divide(10, 2) {
        Ok(v) => println!("10 / 2 = {}", v),
        Err(e) => println!("错误: {}", e),
    }
    match divide(10, 0) {
        Ok(v) => println!("10 / 0 = {}", v),
        Err(e) => println!("错误: {}", e),
    }
} 