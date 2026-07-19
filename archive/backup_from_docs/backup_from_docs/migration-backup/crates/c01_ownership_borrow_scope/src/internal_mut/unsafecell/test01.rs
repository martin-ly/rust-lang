use std::cell::UnsafeCell;

/*
UnsafeCell 是一个不安全的类型，
它允许在安全上下文中进行不安全的操作。

它提供了一个内部可变性，允许在不可变引用的情况下修改值。
`UnsafeCell<T>`是所有内部可变性类型的基础，
它告诉编译器内部值可能被修改，即使通过不可变引用。

它可以用于实现内部可变性，但需要谨慎使用，
因为它可能会导致数据竞争和 undefined behavior。
*/

#[allow(unused)]
struct MyCell<T> {
    value: UnsafeCell<T>,
}

#[allow(unused)]
impl<T> MyCell<T> {
    fn new(value: T) -> Self {
        MyCell {
            value: UnsafeCell::new(value),
        }
    }

    fn get(&self) -> &T {
        unsafe { &*self.value.get() }
    }

    fn set(&self, value: T) {
        unsafe {
            *self.value.get() = value;
        }
    }
}

#[allow(unused)]
fn unsafecell_test() {
    let cell = MyCell::new(5);
    println!("Value: {}", *cell.get()); // 输出: Value: 5
    cell.set(10);
    println!("New value: {}", *cell.get()); // 输出: New value: 10
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unsafecell01() {
        unsafecell_test();
    }
}
