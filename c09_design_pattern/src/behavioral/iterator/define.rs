// 定义一个迭代器 trait
pub trait IteratorTrait<T> {
    fn next(&mut self) -> Option<T>;
}

// 定义一个集合结构体
pub struct Collection<T> {
    items: Vec<T>,
}

// 实现 Collection 的构造函数
impl<T> Collection<T> {
    pub fn new() -> Self {
        Collection { items: Vec::new() }
    }

    pub fn add(&mut self, item: T) {
        self.items.push(item);
    }
}

// 实现 IteratorTrait trait 为 Collection
impl<T> IteratorTrait<T> for Collection<T> {
    fn next(&mut self) -> Option<T> {
        if self.items.is_empty() {
            None
        } else {
            Some(self.items.remove(0))
        }
    }
}


/*
说明
    IteratorTrait: 
        定义了一个泛型迭代器 trait，包含一个 next 方法。
    Collection: 
        定义了一个集合结构体，内部使用 Vec<T> 存储元素。
    实现 IteratorTrait: 
        为 Collection 实现了 IteratorTrait，使其能够返回集合中的下一个元素。
    使用示例: 
        在 main 函数中创建一个 Collection 实例，添加元素并迭代输出。
*/
#[allow(unused)]
fn iterator() {
    let mut collection = Collection::new();
    collection.add(1);
    collection.add(2);
    collection.add(3);

    while let Some(item) = collection.next() {
        println!("{}", item);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_iterator01() {
        iterator();
    }
}

