/*
    Rust 的模式匹配是一种强大的控制流机制，
    允许根据数据值的结构进行分支。
  
    模式匹配可以被视为一种自然变换，它将输入数据的不同形态映射到不同的处理逻辑。
*/



#[allow(unused)]
pub fn test_pattern_match() {
    let x = 5;

    match x {
        1 => println!("x is 1"),
        2 => println!("x is 2"),
        _ => println!("x is something else"),
    }
}

/*
模式匹配（Pattern Matching）与控制结构（Control Structure）：
组合关系：
    模式匹配是一种特殊的控制结构，它允许根据数据的结构和内容进行分支。
    它可以看作是对控制流的扩展，提供更强大的条件判断能力。
形式：
    例如，使用模式匹配：
*/
#[allow(unused)]
pub fn test_pattern_match_2() -> () {
    let value = Some(10);
    match value {
        Some(x) => println!("Value is: {}", x), // 控制结构
        None => println!("No value"), // 控制结构
    }
}


