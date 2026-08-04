// 错误处理案例：Option类型与可选值
// 理论映射：对应“Option类型”与“错误安全性”定理（见 01_formal_error_model.md 附录）

fn get_first(v: &[i32]) -> Option<i32> {
    v.get(0).copied()
}

fn main() {
    let v = vec![1, 2, 3];
    match get_first(&v) {
        Some(x) => println!("第一个元素: {}", x),
        None => println!("无元素"),
    }
    let empty: Vec<i32> = vec![];
    match get_first(&empty) {
        Some(x) => println!("第一个元素: {}", x),
        None => println!("无元素"),
    }
} 