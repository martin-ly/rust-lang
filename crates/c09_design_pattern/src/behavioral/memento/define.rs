// 定义备忘录结构体
#[allow(unused)]
#[derive(Clone)]
struct Memento<T> {
    state: T,
}

// 定义发起人结构体
#[allow(unused)]
#[derive(Clone)]
struct Originator<T> {
    state: T,
}

impl<T> Originator<T> 
where 
    T: Clone, // 确保 T 可以克隆
{
    fn new(state: T) -> Self {
        Originator { state }
    }

    fn set_state(&mut self, state: T) {
        self.state = state;
    }

    fn save(&self) -> Memento<T> {
        Memento {
            state: self.state.clone(), // 保存当前状态
        }
    }

    fn restore(&mut self, memento: Memento<T>) {
        self.state = memento.state; // 恢复状态
    }
}

// 定义管理者结构体
#[allow(unused)]
#[derive(Clone)]
struct Caretaker<T> {
    mementos: Vec<Memento<T>>,
}

impl<T> Caretaker<T> {
    fn new() -> Self {
        Caretaker { mementos: Vec::new() }
    }

    fn add_memento(&mut self, memento: Memento<T>) {
        self.mementos.push(memento);
    }

    fn get_memento(&self, index: usize) -> Option<&Memento<T>> {
        self.mementos.get(index)
    }
}

/*
代码说明：
Memento：用于保存状态的结构体，使用泛型 T。
Originator：发起人，持有当前状态并提供保存和恢复状态的方法。
Caretaker：管理者，负责存储和管理备忘录。
*/

// 示例使用
#[allow(unused)]
fn memento_test() {
    let mut originator = Originator::new("初始状态".to_string());
    let mut caretaker = Caretaker::new();

    // 保存状态
    caretaker.add_memento(originator.save());

    // 修改状态
    originator.set_state("修改后的状态".to_string());

    // 恢复状态
    if let Some(memento) = caretaker.get_memento(0) {
        originator.restore(memento.clone());
    }

    // 输出当前状态
    println!("当前状态: {}", originator.state);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memento01() {
        memento_test();
    }
}
