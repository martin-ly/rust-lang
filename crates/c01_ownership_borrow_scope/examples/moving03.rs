fn transfer_elements<T>(source: &mut Vec<T>, destination: &mut Vec<T>) {
    // 使用 drain 方法转移元素
    destination.extend(source.drain(..));
}

fn main() {
    let mut source = vec![1, 2, 3, 4, 5];
    let mut destination: Vec<i32> = Vec::new();

    println!("Before transfer:");
    println!("Source: {:?}", source);
    println!("Destination: {:?}", destination);

    // 转移元素
    transfer_elements(&mut source, &mut destination);

    println!("After transfer:");
    println!("Source: {:?}", source); // source 现在为空
    println!("Destination: {:?}", destination); // destination 包含转移的元素
}

// 该代码说明：
//函数 transfer_elements：接受两个可变引用的 Vec，
//并使用 drain 方法将 source 中的元素转移到 destination。
//main 函数：创建两个 Vec，一个用于存储源元素，一个用于存储目标元素。
//然后调用 transfer_elements 函数转移元素。
//移动语义：
//  在这个示例中，drain 方法会转移元素的所有权，确保内存安全。
//  由于我们使用的是可变引用，Vec 的所有权不会被转移，
//  您可以在 main 函数中继续使用 source 和 destination。
