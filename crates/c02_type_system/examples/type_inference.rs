//! 类型推断示例：编译器如何推导类型，以及何时需要显式标注。

fn sum<T: std::iter::Sum<T> + Copy>(values: &[T]) -> T {
    values.iter().copied().sum()
}

fn main() {
    // 从初始化表达式推导
    let v = vec![1, 2, 3]; // Vec<i32>

    // 从使用场景推导
    let total: i32 = sum(&v);

    // collect 需要显式目标类型
    let doubled: Vec<i32> = v.iter().map(|x| x * 2).collect();

    // parse 需要 turbofish 或标注
    let parsed = "42".parse::<i32>().expect("valid number");

    // 闭包参数通常可由上下文推导
    let squared: Vec<i32> = doubled.iter().map(|x| x * x).collect();

    println!("total={total}, parsed={parsed}, squared={squared:?}");
}
