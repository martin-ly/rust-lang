/*
在Rust中，切片（slice）是一种对数组或向量（Vec<T>）的视图，
允许你以一种轻量级的方式访问一部分数据。
切片是对一段连续内存的引用，不拥有数据本身，因此它们非常高效。
定义
    类型：切片的类型是 &[T]，其中 T 是切片中元素的类型。
特性：
    动态大小：切片的大小在运行时确定，允许你在不复制数据的情况下访问数组或向量的一部分。
    不可变性：默认情况下，切片是不可变的。如果需要修改切片中的元素，必须使用可变切片（&mut [T]）。
引用：
    切片是对数据的引用，因此它们不会影响原始数据的所有权。
语法
    创建切片的基本语法如下：
    let slice: &[T] = &array[start_index..end_index]; // 从数组创建切片
    let slice: &[T] = &vec[start_index..end_index]; // 从向量创建切片
*/

#[allow(unused)]
// 函数接受切片作为参数
fn print_slice(slice: &[i32]) {
    for &item in slice {
        print!("{} ", item);
    }
    println!(); // 输出换行
}

#[allow(unused)]
pub fn test_slice01() {
    // 创建一个数组
    let arr = [1, 2, 3, 4, 5];

    // 创建一个切片
    let slice: &[i32] = &arr[1..4]; // 切片包含元素 [2, 3, 4]
    println!("Slice: {:?}", slice); // 输出: Slice: [2, 3, 4]

    // 遍历切片
    for &item in slice {
        println!("{}", item); // 输出: 2 3 4
    }

    // 创建一个 Vec
    let vec = vec![10, 20, 30, 40, 50];

    // 从 Vec 创建切片
    let vec_slice: &[i32] = &vec[0..3]; // 切片包含元素 [10, 20, 30]
    println!("Vec Slice: {:?}", vec_slice); // 输出: Vec Slice: [10, 20, 30]

    // 使用切片的长度
    println!("Length of vec_slice: {}", vec_slice.len()); // 输出: Length of vec_slice: 3

    // 创建可变切片
    let mut mutable_vec = vec![1, 2, 3, 4, 5];
    let mutable_slice: &mut [i32] = &mut mutable_vec[1..4]; // 可变切片包含元素 [2, 3, 4]

    // 修改可变切片中的元素
    for item in mutable_slice.iter_mut() {
        *item *= 2; // 将每个元素乘以2
    }
    println!("Mutable Vec after modification: {:?}", mutable_vec); // 输出: Mutable Vec after modification: [1, 4, 6, 8, 5]

    // 切片与数组的比较
    let another_arr = [10, 20, 30, 40, 50];
    let another_slice: &[i32] = &another_arr[2..]; // 切片包含元素 [30, 40, 50]
    println!("Another Slice: {:?}", another_slice); // 输出: Another Slice: [30, 40, 50]

    // 使用切片作为函数参数
    print_slice(&another_slice); // 输出: 30 40 50
}

#[allow(unused)]
pub fn test_slice02() {
    let arr = [1, 2, 3, 4, 5];
    let slice = &arr[1..4]; // [2, 3, 4]
    let sub_slice = &slice[1..]; // [3, 4]
    println!("Slice: {:?}", slice); // 输出: Slice: [2, 3, 4]
    println!("Sub Slice: {:?}", sub_slice); // 输出: Sub Slice: [3, 4]

    let mut numbers = [5, 3, 1, 4, 2];
    let slice = &mut numbers[1..4]; // [3, 1, 4]
    slice.sort(); // 对切片进行排序
    println!("{:?}", numbers); // 输出: [5, 1, 3, 4, 2]
    
    //Rust中的字符串切片（&str）是对字符串的不可变视图，允许你处理字符串的一部分。
    let s = String::from("Hello, world!");
    let slice = &s[0..5]; // 切片包含 "Hello"
    println!("{}", slice); // 输出: Hello

    // 字符串切片可以转换为字符串
    let s = String::from("Hello, world!");
    let slice = &s[0..5]; // 切片包含 "Hello"
    let string_slice = slice.to_string(); // 将切片转换为字符串
    println!("{}", string_slice); // 输出: Hello

}

#[allow(unused)]
pub fn test_slice03() {
    let text = "The quick brown fox jumps over the lazy dog";
    
    // 创建字符串切片
    let slice = &text[16..19]; 
    // 切片包含 "fox"
    println!("Slice: {}", slice); 
    // 输出: Slice: fox

    // 统计单词数量
    let words: Vec<&str> = text.split_whitespace().collect();
    println!("Words: {:?}", words); 
    // 输出: Words: ["The", "quick", "brown", "fox", "jumps", "over", "the", "lazy", "dog"]

    // 使用切片进行分析
    let first_word = words[0]; 
    // 获取第一个单词
    let last_word = words[words.len() - 1]; 
    // 获取最后一个单词
    println!("First word: {}, Last word: {}", first_word, last_word); 
    // 输出: First word: The, Last word: dog

    // 反转单词
    let reversed_words: Vec<&str> = words.iter().rev().cloned().collect();
    println!("Reversed words: {:?}", reversed_words); 
    // 输出: Reversed words: ["dog", "lazy", "the", "over", "jumps", "fox", "brown", "quick", "The"]
    println!("Reversed words: {}", reversed_words.join(" "));
    // 输出: Reversed words: dog lazy the over jumps fox brown quick The

    println!("Words: {}", words.join(" "));
    // 输出: Words: The quick brown fox jumps over the lazy dog
}

