/*
    控制结构是编程语言中用于控制程序流程的结构。
    Rust 中的控制结构包括条件语句、循环、函数等。
    包括条件语句（如 if、match）、循环（如 for、while）等。
    
    控制结构可以被视为组合态射，它们根据条件选择不同的执行路径，
    将输入（如变量、常量）映射到输出（如程序流程）。

*/


#[allow(unused)]
pub fn test_control_struct() {
    let x = 5;

    if x > 0 {
        println!("x is positive");
    } else {
        println!("x is negative");
    }
}  


/*
控制结构（Control Structure）与表达式（Expression）：
组合关系：
    控制结构通过条件和循环来控制表达式的执行流。
    控制结构本身可以是表达式（如 if 表达式），并根据条件返回不同的值。
形式：
    例如，if 表达式的使用：
*/
#[allow(unused)]
pub fn test_control_struct_2() {
    let condition = true;
    let result = if condition { 1 } else { 0 }; // 控制结构作为表达式
    println!("result is {}", result);
}




