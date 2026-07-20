// 性能优化：数据并行示例 Performance Optimization: Data Parallelism Example
use rayon::prelude::*;

fn main() {
    let v = (1..=1000).collect::<Vec<_>>();
    let sum: i32 = v.par_iter().map(|x| x * 2).sum();
    println!("Sum: {}", sum);
} 