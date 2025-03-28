/*
在Rust中，Vec<T> 是一个动态数组类型，用于存储一组相同类型的元素。
与固定大小的数组不同，Vec 可以在运行时动态调整其大小，适合需要频繁添加或删除元素的场景。
定义
    类型：Vec<T>，其中 T 是向量中元素的类型。
特性：
    动态大小：Vec 可以在运行时根据需要增加或减少元素的数量。
    内存管理：Rust会自动处理内存分配和释放，确保内存安全。
    随机访问：支持通过索引快速访问元素。
    可变性：默认情况下，Vec 是可变的，可以在运行时修改其内容。

语法

创建一个 Vec 的基本语法如下：
    let vec_name: Vec<T> = Vec::new(); // 创建一个空的Vec
    let vec_name = vec![value1, value2, ..., valueN]; // 使用宏创建并初始化Vec
*/

#[allow(unused)]
pub fn test_vec01() {
    // 创建一个空的 Vec
    let mut numbers: Vec<i32> = Vec::new();

    // 向 Vec 中添加元素
    numbers.push(1);
    numbers.push(2);
    numbers.push(3);
    println!("After pushing: {:?}", numbers); // 输出: After pushing: [1, 2, 3]

    // 访问元素
    let first = &numbers[0]; // 使用索引访问
    println!("First element: {}", first); // 输出: First element: 1

    // 使用 get 方法访问元素
    match numbers.get(1) {
        Some(value) => println!("Second element: {}", value), // 输出: Second element: 2
        None => println!("No second element"),
    }

    // 修改元素
    numbers[0] = 10;
    println!("After modification: {:?}", numbers); // 输出: After modification: [10, 2, 3]

    // 删除元素
    numbers.pop(); // 删除最后一个元素
    println!("After pop: {:?}", numbers); // 输出: After pop: [10, 2]

    // 遍历 Vec
    for number in &numbers {
        println!("{}", number); // 输出: 10 2
    }

    // 创建一个包含多个元素的 Vec
    let mut fruits = vec!["Apple", "Banana", "Cherry"];
    fruits.push("Date");
    println!("Fruits: {:?}", fruits); // 输出: Fruits: ["Apple", "Banana", "Cherry", "Date"]

    // 获取 Vec 的长度
    println!("Length of fruits: {}", fruits.len()); // 输出: Length of fruits: 4

    // 清空 Vec
    fruits.clear();
    println!("Fruits after clear: {:?}", fruits); // 输出: Fruits after clear: []
}

#[allow(unused)]
pub fn test_vec02() {
    let mut numbers = vec![1, 2, 3];
    numbers.insert(1, 10); // 在索引1处插入10
    println!("{:?}", numbers); // 输出: [1, 10, 2, 3]

    let mut numbers = vec![1, 2, 3, 4];
    numbers.remove(2); // 删除索引2的元素
    println!("{:?}", numbers); // 输出: [1, 2, 4]


    let numbers = vec![1, 2, 3, 4];
    if let Some(pos) = numbers.iter().position(|&x| x == 3) {
        println!("Found 3 at index: {}", pos); // 输出: Found 3 at index: 2
    } else {
        println!("3 not found");
    }

    let mut numbers = vec![4, 2, 3, 1];
    numbers.sort(); // 对 Vec 进行排序
    println!("{:?}", numbers); // 输出: [1, 2, 3, 4]


    let mut numbers = vec![1, 2, 3, 4];
    numbers.reverse(); // 反转 Vec
    println!("{:?}", numbers); // 输出: [4, 3, 2, 1]

    // Vec 在添加元素时可能会多次分配内存，导致性能下降。
    // 可以使用 with_capacity 方法预先分配足够的内存，以减少分配次数
    let mut numbers = Vec::with_capacity(10); // 预分配容量为10
    for i in 0..10 {
        numbers.push(i);
    }
    println!("{:?}", numbers); // 输出: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

    //当需要复制Vec时，使用clone方法。
    //注意，克隆会导致性能开销，尤其是当Vec中包含大量数据时。
    let original = vec![1, 2, 3];
    let copy = original.clone(); // 克隆 Vec
    println!("{:?}", copy); // 输出: [1, 2, 3]

    // 使用迭代器遍历Vec
    let numbers = vec![1, 2, 3, 4, 5];
    for number in &numbers {
        println!("{}", number); // 输出: 1 2 3 4 5
    }

    // 使用迭代器遍历Vec并修改元素
    let mut numbers = vec![1, 2, 3, 4, 5];
    for number in &mut numbers {
        *number *= 2; // 将每个元素乘以2
    }
    println!("{:?}", numbers); // 输出: [2, 4, 6, 8, 10]


}

