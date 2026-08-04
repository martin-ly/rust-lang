/*
在 Rust 中，切片（Slice）是一种动态大小的视图，用于引用数组或其他集合的一部分。
切片提供了一种安全的方式来访问集合中的元素，而不需要复制数据。
1. 定义
    切片是一个指向数组或其他集合的一部分的引用。
    它包含两个部分：
        指针：指向切片的第一个元素。
        长度：切片中元素的数量。
    切片的类型通常表示为 &[T]，其中 T 是切片中元素的类型。
2. 核心概念
    动态大小：
        切片的大小在运行时确定，因此它们可以引用任意长度的数组或集合。
    不可变和可变切片：
        切片可以是不可变的（&[T]）或可变的（&mut [T]），这取决于你是否希望修改切片中的元素。
    借用：
        切片是对数据的借用，遵循 Rust 的所有权和借用规则。切片是move语义。

切片之间的赋值
    不可变切片：
        当你将一个不可变切片赋值给另一个不可变切片时，两个切片都将引用相同的数据。
    可变切片：
        当你将一个可变切片赋值给另一个可变切片时，
        两个切片也将引用相同的数据，并且可以通过其中一个切片修改数据。
总结
    在 Rust 中，切片之间的赋值是将一个切片的引用赋值给另一个切片。
    不可变切片和可变切片之间的赋值都遵循相同的规则，
    切片引用的数据不会被复制，而是共享相同的内存。

    在 Rust 中，切片之间的赋值并不违反可变引用的规则，
    因为在任何时刻，只有一个可变引用是有效的。
    当你将一个可变切片赋值给另一个可变切片时，
    实际上是将一个引用赋值给另一个引用，而不是同时存在两个可变引用。
    等价的说，可变切片之间的赋值，实际上是move语义。

    切片不能直接用于元组，因为元组的元素类型可以不同且大小固定。
    切片主要用于数组和向量等动态大小的集合。
    如果需要处理元组中的元素，可以考虑将其提取到数组或向量中。

不可变切片：
    虽然不可变切片本身不实现 Copy trait，但它的行为类似于复制，
    因为你可以有多个不可变切片同时引用同一数据。
    它们允许多个引用同时存在，且不会引发所有权问题。
可变切片：
    可变切片遵循移动语义的原则。
    在同一时间内，只能有一个可变引用指向某个数据，这确保了数据的安全性和一致性。

*/

#[allow(unused)]
pub fn test_array_slice_define() -> () {
    // 定义一个数组
    let arr = [1, 2, 3, 4, 5];

    // 创建一个切片，引用数组的前 3 个元素
    let slice: &[i32] = &arr[0..3]; // 切片包含 arr[0], arr[1], arr[2]

    // 打印切片的内容
    println!("Slice: {:?}", slice); // 打印: Slice: [1, 2, 3]

    // 创建一个可变数组
    let mut arr2 = [10, 20, 30, 40, 50];

    // 创建一个可变切片，引用数组的后 3 个元素
    let slice_mut: &mut [i32] = &mut arr2[2..5]; // 切片包含 arr2[2], arr2[3], arr2[4]

    // 修改切片中的元素
    for elem in slice_mut.iter_mut() {
        *elem += 5; // 每个元素加 5
    }

    // 打印修改后的数组
    println!("Modified array: {:?}", arr2); // 打印: Modified array: [10, 20, 35, 45, 55]
}

#[allow(unused)]
pub fn test_array_slice() -> () {
    let numbers: [i32; 5] = [1, 2, 3, 4, 5];
    let slice: &[i32] = &numbers[1..3]; // 创建一个从索引 1 到索引 3 的切片
    println!("Slice: {:?}", slice); // 打印: Slice: [2, 3]
}

#[allow(unused)]
pub fn test_array_slice_str() -> () {
    let fruits: [&str; 4] = ["Apple", "Banana", "Cherry", "Date"];
    let slice: &[&str] = &fruits[1..3]; // 创建一个从索引 1 到索引 3 的切片
    println!("Slice: {:?}", slice); // 打印: Slice: ["Banana", "Cherry"]
}

#[allow(unused)]
pub fn test_array_slice_string() -> () {
    let fruits: [String; 4] = [
        String::from("Apple"),
        String::from("Banana"),
        String::from("Cherry"),
        String::from("Date"),
    ];
    let slice: &[String] = &fruits[1..3]; // 创建一个从索引 1 到索引 3 的切片
    println!("Slice: {:?}", slice); // 打印: Slice: ["Banana", "Cherry"]
    println!("fruits: {:?}", fruits); // 打印: fruits: ["Apple", "Banana", "Cherry", "Date"]
}

#[allow(unused)]
pub fn test_array_slice_string_mut_ref() -> () {
    let mut fruits: [String; 4] = [
        String::from("Apple"),
        String::from("Banana"),
        String::from("Cherry"),
        String::from("Date"),
    ];
    let slice: &mut [String] = &mut fruits[1..3]; // 创建一个从索引 1 到索引 3 的切片
    slice[0] = String::from("Orange"); // 修改切片中的第一个元素
    println!("Slice: {:?}", slice); // 打印: Slice: ["Orange", "Cherry"]
    println!("fruits: {:?}", fruits); // 打印: fruits: ["Apple", "Orange", "Cherry", "Date"]
}

#[allow(unused)]
pub fn test_slice_assign() -> () {
    let arr = [10, 20, 30, 40, 50];
    println!("Original array: {:?}", arr);
    // 创建一个不可变切片，引用数组的后 3 个元素
    let slice1: &[i32] = &arr[2..5]; // 切片包含 arr[2], arr[3], arr[4]
    println!("slice1: {:?}", slice1);

    // 赋值给另一个不可变切片 类似copy语义
    let slice2: &[i32] = slice1;
    println!("slice1: {:?}", slice1);
    println!("slice2: {:?}", slice2);

    // 修改切片中的元素
    for elem in slice2.iter() {
        println!("elem: {:?}", elem); // 每个元素加 5
    }

    // 打印修改后的数组
    println!("Modified array: {:?}", arr); // 打印: Modified array: [10, 20, 30, 40, 50]
}

#[allow(unused)]
pub fn test_mut_slice_assign() -> () {
    let mut arr = [10, 20, 30, 40, 50];
    println!("Original array: {:?}", arr);

    // 创建一个可变切片，引用数组的后 3 个元素
    let slice_mut1: &mut [i32] = &mut arr[2..5]; // 切片包含 arr[2], arr[3], arr[4]
    println!("slice_mut1: {:?}", slice_mut1);

    // 在这里，slice_mut1 是唯一的可变引用
    // 赋值给另一个可变切片
    let slice_mut2: &mut [i32] = slice_mut1;
    // slice_mut2 现在引用与 slice_mut1 相同的数据
    // slice_mut1 是move语义 到 slice_mut2
    //println!("slice_mut1: {:?}", slice_mut1);
    println!("slice_mut2: {:?}", slice_mut2);

    // 修改切片中的元素
    for elem in slice_mut2.iter_mut() {
        *elem += 5; // 每个元素加 5
    }

    // 打印修改后的数组
    println!("Modified array: {:?}", arr); // 打印: Modified array: [10, 20, 35, 45, 55]
}

#[allow(unused)]
pub fn test_slice_to_vec() -> () {
    // 定义一个向量
    let vec = vec![1, 2, 3, 4, 5];
    println!("Original vector: {:?}", vec);

    // 创建一个切片，引用向量的前 3 个元素
    let slice: &[i32] = &vec[0..3];

    // 打印原始切片
    println!("Original slice: {:?}", slice);
    // 打印: Original slice: [1, 2, 3]

    // 将切片转换为向量并修改数据
    let mut modified_data = slice.to_vec();
    modified_data.push(6);
    println!("Modified cloned data: {:?}", modified_data);
    // 打印: Modified cloned data: [1, 2, 3, 6]

    // 原始向量保持不变
    println!("Original vector: {:?}", vec);
    // 打印: Original vector: [1, 2, 3, 4, 5]
}

#[allow(unused)]
pub fn test_slice_iter() -> () {
    let mut arr = [1, 2, 3, 4, 5];
    println!("Original array: {:?}", arr);

    let slice_mut: &mut [i32] = &mut arr[1..4]; // 创建可变切片
    println!("{:?}", slice_mut);
    // 修改切片中的元素
    for elem in slice_mut.iter_mut() {
        *elem += 1; // 每个元素加 1
    }

    println!("Modified array: {:?}", arr); // 打印: [1, 3, 4, 5, 5]
}
