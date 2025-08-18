// 基本错误处理示例 Basic Error Handling Example
fn parse_num(s: &str) -> Result<i32, std::num::ParseIntError> {
    s.parse()
}

fn main() {
    match parse_num("42") {
        Ok(n) => println!("Parsed: {}", n),
        Err(e) => println!("Error: {}", e),
    }
} 