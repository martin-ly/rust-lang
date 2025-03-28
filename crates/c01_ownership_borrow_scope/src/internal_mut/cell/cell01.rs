use std::cell::Cell;

/*
`Cell<T>`提供了对简单值的内部可变性，适用于实现`Copy`特性的类型（如整数、布尔值等）。
`Cell<T>`不提供内部值的引用，而是通过值的复制来实现修改，因此只适用于小型数据。
`Cell<T>`不支持所有权转移，因此它不能用于所有权转移的场景。

在Rust中，`Cell<T>`的存在是有必要的，尽管原生类型支持直接复制和修改。
以下是一些原因：

1. **内部可变性**：
`Cell<T>`允许在不可变引用的上下文中修改值。
这对于需要在不可变结构中存储可变状态的情况非常有用。

2. **线程安全**：
`Cell<T>`是非线程安全的，但它提供了一种简单的方式来处理单线程中的内部可变性，
而不需要使用更复杂的同步原语。

3. **性能**：
在某些情况下，使用`Cell<T>`可以避免不必要的克隆和复制，从而提高性能。

4. **简化代码**：
使用`Cell<T>`可以使代码更简洁，特别是在需要频繁修改值的情况下。

总之，虽然原生类型可以直接复制和修改，
但`Cell<T>`提供了更灵活的方式来处理内部可变性和状态管理。
*/

#[allow(unused)]
struct Counter {
    count: Cell<i32>,
}

#[allow(unused)]
impl Counter {
    fn new() -> Self {
        Counter { count: Cell::new(0) }
    }

    fn increment(&self) {
        self.count.set(self.count.get() + 1);
    }

    fn get_count(&self) -> i32 {
        self.count.get()
    }
}

#[allow(unused)]
fn cell_test() {
    let counter = Counter::new();
    counter.increment();
    counter.increment();
    // 输出: Count: 2
    println!("Count: {}", counter.get_count()); 
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cell01() {
        cell_test();
    }
}
