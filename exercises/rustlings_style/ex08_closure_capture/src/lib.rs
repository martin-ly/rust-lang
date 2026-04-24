// 练习: 闭包捕获方式
// 目标: 修复闭包捕获可变引用的问题
// 考点: move 关键字、FnMut

pub fn double_all(values: &mut [i32]) {
    let doubler = || {
        for v in values.iter_mut() {
            *v *= 2;
        }
    };
    doubler();
    // 错误: 如果闭包以可变方式捕获了 values，这里再次使用会冲突
    println!("{:?}", values);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_double_all() {
        let mut v = vec![1, 2, 3];
        double_all(&mut v);
        assert_eq!(v, vec![2, 4, 6]);
    }
}
