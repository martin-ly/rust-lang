/*
闭包是 Rust 中的一种匿名函数，可以捕获并存储其周围环境中的变量。
闭包可以被视为一种特殊的态射，它们将输入（如变量、常量）映射到输出（如函数结果）。

闭包是可以捕获其环境的函数。
在 Rust 中，闭包可以作为表达式使用，允许在控制流中灵活地传递和执行代码。

闭包可以被视为态射的高阶形式，它们可以接受其他态射作为参数。
*/

#[allow(unused)]
pub fn test_closure() {
    let x = 5;

    let closure = |y| y + x;
    println!("{}", closure(10));
}

/*
闭包（Closure）与表达式（Expression）：
组合关系：
    闭包可以作为表达式使用，并且可以在控制结构中传递和执行。
    闭包允许将逻辑封装在一个可重用的单元中。
形式：
    例如，使用闭包作为参数：
*/
#[allow(unused)]
pub fn test_closure_2() -> () {
    let add = |x, y| x + y; // 闭包
    let result = add(2, 3); // 表达式
    println!("result is {}", result);
}

#[allow(unused)]
fn call_fn<F: Fn()>(f: F) {
    f(); // 调用 Fn 闭包
}

#[allow(unused)]
fn call_fn_mut<F: FnMut()>(mut f: F) {
    f(); // 调用 FnMut 闭包
}

#[allow(unused)]
fn call_fn_once<F: FnOnce()>(f: F) {
    f(); // 调用 FnOnce 闭包
}

#[allow(unused)]
pub fn test_closure01() {
    let x = 10;

    // Fn 闭包
    let fn_closure = || println!("Fn closure: {}", x);
    call_fn(fn_closure);
    call_fn(fn_closure);

    // FnMut 闭包
    let mut y = 5;
    let fn_mut_closure = || {
        y += 1;
        println!("FnMut closure: {}", y);
    };
    call_fn_mut(fn_mut_closure);
    //call_fn_mut(fn_mut_closure); // 错误：`fn_mut_closure` 已经移动

    // FnOnce 闭包
    let s = String::from("Hello");
    let fn_once_closure = move || println!("FnOnce closure: {}", s);
    call_fn_once(fn_once_closure);
    //call_fn_once(fn_once_closure); // 错误：`fn_once_closure` 已经移动
}
