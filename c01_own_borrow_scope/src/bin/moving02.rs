fn remove_item<T: PartialEq>(vec: &mut Vec<T>, item: T) {
    // 使用 retain 方法保留不等于 item 的元素
    vec.retain(|x| *x != item);
}

fn main() {
    let mut numbers = vec![1, 2, 3, 4, 5, 3, 6];

    println!("Before removal: {:?}", numbers);
    
    // 删除所有值为 3 的元素
    remove_item(&mut numbers, 3);

    println!("After removal: {:?}", numbers);
}

// 该代码说明：
//函数 remove_item：接受一个可变引用的 Vec 和要删除的元素。
//使用 retain 方法来保留不等于 item 的元素，从而实现删除。
//main 函数：创建一个包含多个整数的 Vec，然后调用 remove_item 函数删除所有值为 3 的元素。
//移动语义：
//在这个示例中，retain 方法会在内部处理元素的移动和删除，确保内存安全。
//由于我们使用的是可变引用，Vec 的所有权不会被转移，您可以在 main 函数中继续使用 numbers。