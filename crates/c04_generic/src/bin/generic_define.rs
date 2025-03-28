
use c04_generic::generic_define::*;

fn main() {
    // 使用泛型结构体
    let point = Point { x: 1, y: 2 };
    println!("Point: ({}, {})", point.x, point.y);

    // 使用特征
    let my_string = String::from("Hello, Rust!");
    summarize_item(my_string);

    let numbers = vec![34, 50, 25, 100, 65];
    println!("numbers: {:?}", numbers);
    let largest = largest(&numbers);
    println!("The largest number is {}", largest);
    println!("numbers: {:?}", numbers);


    let string1 = String::from("long string");
    let string2 = String::from("short");

    let result = longest(string1.as_str(), string2.as_str());
    println!("The longest string is {}", result);

    // 生命周期参数 不匹配
    // 错误：`string4` 在 `result` 的生存期结束之前就已经被释放了
    /* 
    let string3 = String::from("long string is long");
    let result;
    {
        let string4 = String::from("xyz");
        result = longest(string3.as_str(), string4.as_str());
    }
    println!("The longest string is {}", result);
    */


    let dog = Dog {
        name: String::from("Buddy"),
    };
    print_description(dog);

    hashmap_test();
    
}
