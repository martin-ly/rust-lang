// unsafe代码安全性验证示例
// 工程意义：演示Rust unsafe块下的内存操作如何通过形式化断言与工具约束提升安全性，适用于Kani/Creusot等工具验证

fn main() {
    let mut data = vec![1, 2, 3];
    let ptr = data.as_mut_ptr();
    unsafe {
        // 形式化前置条件：ptr有效且指向data的合法范围
        *ptr.add(1) = 42; // 修改第二个元素
    }
    assert_eq!(data, vec![1, 42, 3]);
}

// 形式化注释：
// 前置条件：ptr = data.as_mut_ptr(), 0 <= 1 < data.len()
// 后置条件：data[1] = 42
// 工具建议：Kani可验证unsafe块边界条件，Creusot可建模不变式与内存安全 