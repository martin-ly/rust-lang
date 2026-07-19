// 示例：理解借用检查器的分析
// 这些示例展示了借用检查器如何分析代码

/// NLL示例：非词法生命周期
/// 在NLL之前这会编译失败
pub fn nll_example() {
    let mut x = 5;
    let y = &x;
    
    // y的使用
    if false {
        println!("{}", y);
    }
    // y的生命周期在这里结束（最后使用点）
    
    // 现在可以可变借用x了
    x = 10;
    println!("{}", x);
}

/// 两阶段借用示例
/// vec.push可以同时使用&mut和&借用
pub fn two_phase_borrow() {
    let mut vec = vec![1, 2, 3];
    
    // 两阶段借用允许这样写
    vec.push(vec.len() as i32);
    
    println!("{:?}", vec);
}

/// 借用分裂示例
/// 可以同时可变借用数组的不同部分
pub fn borrow_splitting(arr: &mut [i32]) {
    if arr.len() >= 2 {
        let (first, rest) = arr.split_at_mut(1);
        first[0] = 42;
        rest[0] = 100;
    }
}

/// 生命周期省略示例
/// 编译器会自动推断生命周期
pub fn lifetime_elision_example(s: &str) -> &str {
    &s[0..1]
}

/// 复杂借用场景
/// 借用检查器会追踪每个引用的生命周期
pub fn complex_borrowing() {
    let mut data = vec![1, 2, 3, 4, 5];
    
    {
        let first = &data[0];
        println!("First: {}", first);
    } // first的借用在这里结束
    
    data.push(6); // 现在可以修改data
    
    let last = &data[data.len() - 1];
    println!("Last: {}", last);
}

/// 可变借用不重叠示例
pub fn non_overlapping_mut_borrows() {
    let mut point = (0, 0);
    
    // 不能同时可变借用
    // let x = &mut point.0;
    // let y = &mut point.1;  // 错误！
    
    // 但可以分别借用
    {
        let x = &mut point.0;
        *x = 10;
    }
    {
        let y = &mut point.1;
        *y = 20;
    }
    
    println!("Point: {:?}", point);
}

/// Drop检查示例
/// 借用检查器会确保drop时没有活跃借用
pub fn drop_check_example() {
    let s = String::from("hello");
    let r = &s;
    
    println!("{}", r);
    // s在这里drop，借用检查器确保r不再使用
}

/// 结构体字段借用
/// 可以独立借用结构体的不同字段
struct Point {
    x: i32,
    y: i32,
}

pub fn struct_field_borrowing() {
    let mut point = Point { x: 0, y: 0 };
    
    let x = &mut point.x;
    let y = &mut point.y; // 可以！不同字段
    
    *x = 10;
    *y = 20;
    
    println!("Point: ({}, {})", point.x, point.y);
}

/// 闭包捕获分析
/// 借用检查器会分析闭包捕获的方式
pub fn closure_capture() {
    let mut x = 5;
    
    {
        let mut add_to_x = |y| x += y;
        add_to_x(10);
    } // 闭包的可变借用在这里结束
    
    println!("x = {}", x);
}

fn main() {
    nll_example();
    two_phase_borrow();
    
    let mut arr = [1, 2, 3, 4, 5];
    borrow_splitting(&mut arr);
    
    let s = "hello";
    println!("{}", lifetime_elision_example(s));
    
    complex_borrowing();
    non_overlapping_mut_borrows();
    drop_check_example();
    struct_field_borrowing();
    closure_capture();
}

