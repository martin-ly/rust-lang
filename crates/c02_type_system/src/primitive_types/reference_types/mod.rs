/*

在 Rust 中，借用（Borrowing）和引用（Reference）是非常重要的概念，
它们与类型的大小（Sized）有着密切的关系。
借用和引用在Rust中具有等价关系的概念。
以下是对借用或者引用类型是否 Sized 的解释，以及如何理解这一点。
1. 借用和引用的定义
    借用：
        借用是指在不获取所有权的情况下使用某个值。
        借用可以是可变借用（&mut T）或不可变借用（&T）。
    引用：引用是指向某个值的指针。
        引用可以是不可变引用（&T）或可变引用（&mut T）。
2. 借用类型的 Sized 特性

2.1 引用类型的大小
    引用是 Sized：在 Rust 中，引用类型（如 &T 和 &mut T）是 Sized 的。
    这是因为引用本身的大小是固定的，
    引用的大小在编译时是已知的（通常是指针的大小，通常为 4 字节或 8 字节，具体取决于平台）。

2.2 借用的类型
    借用的值的大小：借用的值（即被引用的值）可能是 Sized 或者 ?Sized。
    例如，借用一个数组（&[T]）时，数组的大小是固定的，因此它是 Sized。
    但是，借用一个切片（&[T]）时，切片本身是动态大小的，因此它不是 Sized。

*/
