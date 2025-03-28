/*
浮点数类型用于表示带小数的数值。
1. Rust 提供了两种浮点数类型：
    1.1 f32: 32 位浮点数，单精度。
    1.2 f64: 64 位浮点数，双精度（默认浮点数类型）。

2. 注意事项
    2.1 精度：f32 和 f64 的精度不同，f64 提供更高的精度，但占用更多内存。
    2.2 NaN 和 Infinity：浮点数支持特殊值，如 NaN（Not a Number）和正负无穷大。
3. 两种浮点数类型的最大值：
    3.1 f32（32 位浮点数）
        最大值：f32::MAX
        值：约为 3.40282347e+38
    3.2 f64（64 位浮点数）
        最大值：f64::MAX
        值：约为 1.7976931348623157e+308

4. 特殊值
    4.1 NaN（Not a Number）
        表示无效或未定义的数值。（f32::NAN,  f64::NAN）
        定义：NaN 是一个特殊的浮点值，表示未定义或不可表示的值，例如 0 除以 0。
        特性：NaN 与任何值（包括自身）比较时都返回 false。
    4.2 Infinity（无穷大）
        表示超出数值范围的值。（f32::INFINITY,  f64::INFINITY）
        定义：Infinity 是一个特殊的浮点值，表示超出数值范围的值，例如 1.0 / 0.0。
        特性：Infinity 与任何值（包括自身）比较时都返回 true。
    4.3 -Infinity（负无穷大）
        表示超出数值范围的负值。（f32::NEG_INFINITY, f64::NEG_INFINITY）
        定义：-Infinity 是一个特殊的浮点值，表示超出数值范围的负值，例如 -1.0 / 0.0。
        特性：-Infinity 与任何值（包括自身）比较时都返回 true。
*/

#[allow(unused)]
pub fn float_operation() {
    let pi: f64 = 3.14159; // 64 位浮点数
    let e: f32 = 2.71828;  // 32 位浮点数

    let sum = pi + e as f64; // 将 e 转换为 f64
    println!("Sum of pi and e: {}", sum); // 打印: Sum of pi and e: 5.85987

    // 指定小数位数
    println!("Value of pi (2 decimal places): {:.2}", pi);
    println!("Value of e (3 decimal places): {:.3}", e);

    // 获取 f32 和 f64 的最大值
    let max_f32 = f32::MAX;
    let max_f64 = f64::MAX;
    // 打印最大值 科学计数法
    println!("Maximum value of f32: {:.16e}", max_f32); // 打印: Maximum value of f32: 3.4028234663852886e38
    println!("Maximum value of f64: {:.16e}", max_f64); // 打印: Maximum value of f64: 1.7976931348623157e308
}

#[allow(unused)]
pub fn float_operation_2() {
    // 创建 NaN
    let nan_value: f64 = f64::NAN;
    println!("nan_value value: {}", nan_value); // 打印: NaN value: NaN
    println!("nan_value > 1.0 : {}", nan_value > 1.0); // 打印: nan_value > 1.0 : false

    // 检查 NaN
    if nan_value.is_nan() {
        println!("The nan_value value is NaN."); // 打印: The value is NaN.
    }

    // 创建正无穷大和负无穷大
    let pos_infinity: f64 = f64::INFINITY;
    let neg_infinity: f64 = f64::NEG_INFINITY;

    println!("Positive Infinity: {}", pos_infinity); // 打印: Positive Infinity: inf
    println!("Negative Infinity: {}", neg_infinity); // 打印: Negative Infinity: -inf

    // 测试与无穷大的运算
    let result1 = pos_infinity + 1.0; // 正无穷大加任何数仍然是正无穷大
    let result2 = neg_infinity - 1.0; // 负无穷大减去任何数仍然是负无穷大

    println!("Positive Infinity + 1.0 = {}", result1); // 打印: Positive Infinity + 1.0 = inf
    println!("Negative Infinity - 1.0 = {}", result2); // 打印: Negative Infinity - 1.0 = -inf

    // 测试 NaN 与其他值的运算
    let result3 = nan_value + 1.0; // NaN 加任何数仍然是 NaN
    println!("NaN + 1.0 = {}", result3); // 打印: NaN + 1.0 = NaN
}
