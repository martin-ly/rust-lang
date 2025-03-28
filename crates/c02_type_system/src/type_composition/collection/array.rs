/*
在Rust中，`Array<T, N>` 是一种固定大小的数组类型，用于存储一组相同类型的元素。
以下是对Rust数组的综合全面定义、解释和示例。
## 定义
- **类型**：`Array<T, N>`，其中 `T` 是数组中元素的类型，`N` 是数组的大小（在编译时确定）。
- **特性**：
  - **固定大小**：数组的大小在编译时确定，不能动态改变。
  - **连续内存**：数组中的元素在内存中是连续存储的，这使得访问速度非常快。
  - **类型安全**：Rust的类型系统确保数组中的所有元素都是相同类型的。
## 语法
数组的基本语法如下：
```rust
let array_name: [T; N] = [value1, value2, ..., valueN];
```

## 注意事项
- **不可变性**：默认情况下，数组是不可变的。如果需要修改数组的元素，必须使用 `mut` 关键字。
  ```rust
  fn main() {
      let mut numbers: [i32; 5] = [1, 2, 3, 4, 5];
      numbers[0] = 10; // 修改第一个元素
      println!("{:?}", numbers); // 输出: [10, 2, 3, 4, 5]
  }
  ```
- **越界访问**：访问数组时，如果索引超出范围，Rust会在运行时引发恐慌（panic）。
  ```rust
  fn main() {
      let numbers: [i32; 3] = [1, 2, 3];
      // println!("{}", numbers[3]); // 这将导致运行时错误
  }
  ```
## 总结

Rust中的数组是一种强类型、固定大小的容器，适合存储相同类型的元素。
由于其内存连续性，数组提供了高效的访问性能。
通过使用数组，开发者可以在编译时确保数据的类型安全和大小一致性。
*/

#[allow(unused)]
pub fn test_array01() {
    // 创建数组
    let numbers: [i32; 5] = [1, 2, 3, 4, 5];
    println!("{:?}", numbers); // 输出: [1, 2, 3, 4, 5]
}

#[allow(unused)]
pub fn test_array02() {
    // 创建一个包含5个元素的数组，所有元素的值为0
    let zeros: [i32; 5] = [0; 5];
    println!("{:?}", zeros); // 输出: [0, 0, 0, 0, 0]
}

#[allow(unused)]
pub fn test_array03() {
    // 创建一个包含3个字符串的数组
    let fruits: [&str; 3] = ["Apple", "Banana", "Cherry"];
    println!("First fruit: {}", fruits[0]); // 输出: First fruit: Apple
    println!("{:?}", fruits); // 输出: ["Apple", "Banana", "Cherry"]
}

#[allow(unused)]
pub fn test_array04() {
    let numbers: [i32; 5] = [1, 2, 3, 4, 5];
    println!("Length of the array: {}", numbers.len()); // 输出: Length of the array: 5
}

#[allow(unused)]
pub fn test_array05() {
    let matrix: [[i32; 3]; 2] = [[1, 2, 3], [4, 5, 6]];
    println!("{:?}", matrix); // 输出: [[1, 2, 3], [4, 5, 6]]
}


//Rust允许直接比较两个数组，前提是它们的类型和长度相同
#[allow(unused)]
pub fn test_array06() {
    let arr1 = [1, 2, 3];
    let arr2 = [1, 2, 3];
    let arr3 = [4, 5, 6];
    println!("{}", arr1 == arr2); // 输出: true
    println!("{}", arr1 != arr3); // 输出: true
}


