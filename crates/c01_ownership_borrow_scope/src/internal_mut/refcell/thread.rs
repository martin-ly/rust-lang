use std::cell::RefCell;
use std::rc::Rc;

/*
使用 Rc<RefCell<T>>
    Rc 是一个引用计数的智能指针，允许多个所有者共享同一个值，而 RefCell 允许在运行时进行可变借用检查。
    可以在多个地方共享同一个值，并在需要时对其进行修改。
    如果违背借用规则，会在运行时报错。
*/

#[allow(unused)]
struct MyStruct {
    value: i32,
}

#[allow(unused)]
impl MyStruct {
    fn update(&mut self, new_value: i32) {
        self.value = new_value;
    }
}

#[allow(unused)]
pub fn thread_test() {
    let my_struct = Rc::new(RefCell::new(MyStruct { value: 0 }));

    // 获取可变借用
    {
        let mut borrowed = my_struct.borrow_mut();
        borrowed.update(10);
    }
    // 读取值
    println!("Value: {}", my_struct.borrow().value);

    // 获取可变借用
    {
        let mut borrowed = my_struct.borrow_mut();
        borrowed.update(11);
    }
    // 读取值
    println!("Value: {}", my_struct.borrow().value);

    // 获取可变借用 违反了借用规则 运行时错误
    // let mut borrowed = my_struct.borrow_mut();
    // borrowed.update(12);

    // 读取值
    // println!("Value: {}", my_struct.borrow().value);

}


#[allow(unused)]
struct Data {
    value: RefCell<i32>,
}

#[allow(unused)]
impl Data {
    fn new(value: i32) -> Self {
        Data {
            value: RefCell::new(value),
        }
    }

    fn increment(&self) {
        // 通过RefCell获取可变引用
        *self.value.borrow_mut() += 1;
    }
}

#[allow(unused)]
fn thread_test02() {
    let data = Data::new(5);
    data.increment();
    println!("Value: {}", *data.value.borrow()); // 输出: Value: 6
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_thread01() {
        thread_test();
        thread_test02();
    }
}

