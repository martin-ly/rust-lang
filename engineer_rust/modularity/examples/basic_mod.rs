// 模块化：基本模块定义与使用示例 Modularity: Basic Module Example
mod utils {
    pub fn add(a: i32, b: i32) -> i32 { a + b }
}

fn main() {
    let sum = utils::add(2, 3);
    println!("Sum: {}", sum);
} 