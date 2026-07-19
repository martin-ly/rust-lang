// 示例：观察不同优化级别的效果
// 编译命令:
// rustc --emit=llvm-ir -C opt-level=0 examples/compiler_internals/02_optimization_examples.rs -o unopt.ll
// rustc --emit=llvm-ir -C opt-level=3 examples/compiler_internals/02_optimization_examples.rs -o opt.ll
// 对比两个文件的差异

/// 常量传播示例
/// 在O3下会直接计算结果
pub fn constant_propagation() -> i32 {
    let x = 10;
    let y = 20;
    let z = x + y;
    z * 2
}

/// 死代码消除示例
/// unused_variable在优化后会被消除
pub fn dead_code_elimination(flag: bool) -> i32 {
    let x = 42;
    let _unused_variable = 100; // 会被消除
    
    if flag {
        x
    } else {
        0
    }
}

/// 内联示例
/// square函数会被内联到调用点
#[inline]
fn square(x: i32) -> i32 {
    x * x
}

pub fn inlining_example() -> i32 {
    square(5) + square(3)
}

/// 循环展开示例
/// 小循环可能被完全展开
pub fn loop_unrolling() -> i32 {
    let mut sum = 0;
    for i in 0..4 {
        sum += i;
    }
    sum
}

/// 向量化示例
/// 简单的数组操作可能被向量化
pub fn vectorization(arr: &[i32; 8]) -> [i32; 8] {
    let mut result = [0; 8];
    for i in 0..8 {
        result[i] = arr[i] * 2;
    }
    result
}

/// 分支预测示例
/// likely分支会被优化器偏好
pub fn branch_prediction(x: i32) -> i32 {
    if x > 0 {
        // 假设这个分支更常执行
        x * 2
    } else {
        x / 2
    }
}

/// 尾调用优化候选
/// 尾递归可能被优化为循环
pub fn factorial_tail_recursive(n: i32, acc: i32) -> i32 {
    if n == 0 {
        acc
    } else {
        factorial_tail_recursive(n - 1, acc * n)
    }
}

/// 零成本抽象示例
/// Iterator链会被优化为简单循环
pub fn zero_cost_abstraction(vec: Vec<i32>) -> i32 {
    vec.iter()
        .filter(|&&x| x > 0)
        .map(|&x| x * 2)
        .sum()
}

/// 边界检查消除示例
/// 编译器可能会消除一些边界检查
pub fn bounds_check_elimination(arr: &[i32]) -> i32 {
    let mut sum = 0;
    for i in 0..arr.len() {
        sum += arr[i]; // 边界检查可能被消除
    }
    sum
}

fn main() {
    println!("Constant propagation: {}", constant_propagation());
    println!("Dead code elimination: {}", dead_code_elimination(true));
    println!("Inlining: {}", inlining_example());
    println!("Loop unrolling: {}", loop_unrolling());
    
    let arr = [1, 2, 3, 4, 5, 6, 7, 8];
    println!("Vectorization: {:?}", vectorization(&arr));
    println!("Branch: {}", branch_prediction(10));
    println!("Factorial: {}", factorial_tail_recursive(5, 1));
    println!("Zero-cost: {}", zero_cost_abstraction(vec![1, -2, 3, -4, 5]));
}

