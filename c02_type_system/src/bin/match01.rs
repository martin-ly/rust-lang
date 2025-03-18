

#[allow(dead_code)]
pub fn describe_number(num: i32) {
    match num {
        1 | 2 | 3 => println!("One, Two, or Three"),
        4..=10 => println!("Between Four and Ten"),
        _ => println!("Something else"),
    }
}

#[allow(dead_code)]
pub fn describe(value: Option<i32>) {
    match value {
        Some(v) => match v {
            1 => println!("One"),
            2 => println!("Two"),
            _ => println!("Other"),
        },
        None => println!("None"),
    }
}

#[allow(dead_code)]
pub fn describe_number0(num: i32) {
    match num {
        n if n < 0 => println!("Negative number"),
        n if n == 0 => println!("Zero"),
        n if n > 0 => println!("Positive number"),
        _ => unreachable!(), // 这个分支永远不会被匹配到
    }
}

fn main() {
    describe_number0(-5); // 输出: Negative number
    describe_number0(0); // 输出: Zero
    describe_number0(10); // 输出: Positive number

    describe_number(2); // 输出: One, Two, or Three
    describe_number(5); // 输出: Between Four and Ten
    describe_number(11); // 输出: Something else

    describe(Some(1)); // 输出: One
    describe(Some(2)); // 输出: Two
    describe(Some(3)); // 输出: Other
    describe(None); // 输出: None
}
