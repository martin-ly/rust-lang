// 错误处理案例：错误处理组合子
// 理论映射：对应“错误处理组合子”与“错误恢复完备性”定理（见 01_formal_error_model.md 附录）

fn parse_and_double(s: &str) -> Result<i32, String> {
    s.parse::<i32>().map(|x| x * 2).map_err(|e| e.to_string())
}

fn main() {
    match parse_and_double("21") {
        Ok(v) => println!("结果: {}", v),
        Err(e) => println!("错误: {}", e),
    }
    match parse_and_double("abc") {
        Ok(v) => println!("结果: {}", v),
        Err(e) => println!("错误: {}", e),
    }
} 