/*
在 Rust 中，位操作主要针对整数类型进行。这些基础类型包括：

1. 整数类型
Rust 提供了多种整数类型，位操作可以应用于这些类型。整数类型分为有符号和无符号两类：
    1.1 有符号整数（Signed Integers）：
        可以表示正数、负数和零。
        i8: 8 位有符号整数，范围为 -128 到 127。
        i16: 16 位有符号整数，范围为 -32,768 到 32,767。
        i32: 32 位有符号整数，范围为 -2,147,483,648 到 2,147,483,647。
        i64: 64 位有符号整数，范围为 -9,223,372,036,854,775,808 到 9,223,372,036,854,775,807。
        i128: 128 位有符号整数，范围为 -170,141,183,460,684,697,6... 到 170,141,183,460,684,697,6...。
        isize: 根据平台的位数（32 位或 64 位）来决定大小的有符号整数。
        有符号整数使用补码表示法来存储负数。

    1.2 无符号整数（Unsigned Integers）：
        只能表示非负数（0 和正数）。
        u8: 8 位无符号整数，范围为 0 到 255。
        u16: 16 位无符号整数，范围为 0 到 65,535。
        u32: 32 位无符号整数，范围为 0 到 4,294,967,295。
        u64: 64 位无符号整数，范围为 0 到 18,446,744,073,709,551,615。
        u128: 128 位无符号整数，范围为 0 到 340,282,366,920,938,463,463,374,607,431,768,211,456。
        usize: 根据平台的位数（32 位或 64 位）来决定大小的无符号整数。
        无符号整数的所有位都用于表示数值，因此它们的最大值是相同位数的有符号整数的两倍。

2. 位操作支持的基础类型
    位操作可以应用于上述所有整数类型。以下是 Rust 中支持的位操作符：
        按位与（AND）：&
        按位或（OR）：|
        按位异或（XOR）：^
        按位取反（NOT）：!
        左移（Left Shift）：<<
        右移（Right Shift）：>>

3. 位操作的区别
    3.1 按位取反（NOT）操作
        有符号整数：
            按位取反会将所有位反转，包括符号位。
            例如，对于 i8 类型的 5（二进制 0000 0101），取反后变为 -6（二进制 1111 1010）。
        无符号整数：
            按位取反会将所有位反转，但没有符号位。
            例如，对于 u8 类型的 5（二进制 0000 0101），取反后变为 250（二进制 1111 1010）。
    3.2 右移（Right Shift）操作
        有符号整数：
            右移时，符号位会被填充（算术右移），以保持符号的一致性。
            例如，对于 -4（二进制 1111 1100），右移一位后变为 -2（二进制 1111 1110）。
        无符号整数：
            右移时，左侧用 0 填充（逻辑右移）。
            例如，对于 4（二进制 0000 0100），右移一位后变为 2（二进制 0000 0010）。
    3.3 左移（Left Shift）操作
        有符号整数和无符号整数：左移操作在这两种类型中是相同的。
        左移一位相当于乘以 2。
        例如，对于 3（二进制 0000 0011），左移一位后变为 6（二进制 0000 0110）。

*/

#[allow(unused)]
pub fn test_bit_operation() -> () {
    let a: u8 = 5; // 二进制: 0000 0101
    let b: u8 = 3; // 二进制: 0000 0011
    println!("--------------------------------");
    println!("a: {:08b}", a);
    println!("b: {:08b}", b);
    // 按位与
    let and_result = a & b; // 结果: 0000 0001 (1)
    println!(
        "{} & {} = {} (binary: {:08b})",
        a, b, and_result, and_result
    );

    // 按位或
    let or_result = a | b; // 结果: 0000 0111 (7)
    println!("{} | {} = {} (binary: {:08b})", a, b, or_result, or_result);

    // 按位异或
    let xor_result = a ^ b; // 结果: 0000 0110 (6)
    println!(
        "{} ^ {} = {} (binary: {:08b})",
        a, b, xor_result, xor_result
    );

    // 按位取反
    let not_result = !a; // 结果: 1111 1010 (对于 u8 来说是 250)
    println!("!{} = {} (binary: {:08b})", a, not_result, not_result);

    // 左移
    let left_shift_result = a << 1; // 结果: 0000 1010 (10)
    println!(
        "{} << 1 = {} (binary: {:08b})",
        a, left_shift_result, left_shift_result
    );

    // 右移
    let right_shift_result = a >> 1; // 结果: 0000 0010 (2)
    println!(
        "{} >> 1 = {} (binary: {:08b})",
        a, right_shift_result, right_shift_result
    );

    println!("--------------------------------");
}

/*
5 & 3 = 1 (binary: 00000001)
5 | 3 = 7 (binary: 00000111)
5 ^ 3 = 6 (binary: 00000110)
!5 = 250 (binary: 11111010)
5 << 1 = 10 (binary: 00001010)
5 >> 1 = 2 (binary: 00000010)
*/

#[allow(unused)]
pub fn test_bit_operation_2() -> () {
    let signed: i8 = 5; // 有符号整数
    let unsigned: u8 = 5; // 无符号整数
    println!("--------------------------------");
    println!("signed: {:08b}", signed);
    println!("unsigned: {:08b}", unsigned);
    // 按位取反
    let signed_not = !signed; // 结果: -6
    let unsigned_not = !unsigned; // 结果: 250

    println!("Signed NOT: {} (binary: {:08b})", signed_not, signed_not);
    println!(
        "Unsigned NOT: {} (binary: {:08b})",
        unsigned_not, unsigned_not
    );

    // 右移
    let signed_right_shift = signed >> 1; // 结果: 2
    let unsigned_right_shift = unsigned >> 1; // 结果: 2

    println!(
        "Signed >>1: {}, (binary: {:08b})",
        signed_right_shift, signed_right_shift
    );
    println!(
        "Unsigned >>1: {}, (binary: {:08b})",
        unsigned_right_shift, unsigned_right_shift
    );
    println!("--------------------------------");
}

/*
Signed NOT: -6 (binary: 11111010)
Unsigned NOT: 250 (binary: 11111010)
Signed Right Shift: 2
Unsigned Right Shift: 2
*/
