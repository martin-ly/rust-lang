// 定义观察者 trait
pub trait Observer<T> {
    fn update(&self, data: T);
}

// 定义主题 trait
pub trait Subject<T> {
    fn register_observer(&mut self, observer: Box<dyn Observer<T>>);
    fn notify_observers(&self, data: T);
}

// 具体的主题实现
pub struct ConcreteSubject<T> {
    observers: Vec<Box<dyn Observer<T>>>,
}

impl<T> Default for ConcreteSubject<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> ConcreteSubject<T> {
    pub fn new() -> Self {
        ConcreteSubject {
            observers: Vec::new(),
        }
    }
}

impl<T: Clone> Subject<T> for ConcreteSubject<T> {
    fn register_observer(&mut self, observer: Box<dyn Observer<T>>) {
        self.observers.push(observer);
    }

    fn notify_observers(&self, data: T) {
        for observer in &self.observers {
            observer.update(data.clone());
        }
    }
}

// 具体的观察者实现
pub struct ConcreteObserver;

impl Observer<String> for ConcreteObserver {
    fn update(&self, data: String) {
        println!("Received update: {}", data);
    }
}

/*
代码说明：
    Observer：观察者 trait，定义了 update 方法。
    Subject：主题 trait，定义了 register_observer 和 notify_observers 方法。
    ConcreteSubject：具体主题实现，持有观察者列表并提供注册和通知方法。
    ConcreteObserver：具体观察者实现，实现了 Observer trait 的 update 方法。
*/
#[allow(unused)]
// 示例使用
fn observer_test() {
    let mut subject = ConcreteSubject::new();
    let observer = Box::new(ConcreteObserver);

    subject.register_observer(observer);

    subject.notify_observers("Hello, Observer!".to_string());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_observer01() {
        observer_test();
    }
}

// === GATs 借用视图版本（避免数据多次克隆） ===

/// 带借用生命周期的观察者（使用 GATs）
pub trait ObserverRef<T: ?Sized> {
    type Ref<'a>
    where
        T: 'a,
        Self: 'a;

    fn update<'a>(&self, data: Self::Ref<'a>);
}

//

/// 借用视图主题（示例固定观察者/元素类型），通知时仅借用数据
pub struct BorrowingSubjectString {
    observers: Vec<BorrowingObserver>,
}

impl Default for BorrowingSubjectString {
    fn default() -> Self {
        Self::new()
    }
}

impl BorrowingSubjectString {
    pub fn new() -> Self {
        Self { observers: Vec::new() }
    }

    pub fn register_observer(&mut self, observer: BorrowingObserver) {
        self.observers.push(observer);
    }

    pub fn notify_observers(&self, data: &String) {
        for obs in &self.observers {
            obs.update(data);
        }
    }
}

/// 具体观察者（借用数据，不进行克隆）
pub struct BorrowingObserver;

impl ObserverRef<String> for BorrowingObserver {
    type Ref<'a> = &'a String where String: 'a;

    fn update<'a>(&self, data: Self::Ref<'a>) {
        println!("Borrowed update: {}", data);
    }
}

#[cfg(test)]
mod gats_tests {
    use super::*;

    #[test]
    fn test_borrowing_observer() {
        let mut subject = BorrowingSubjectString::new();
        subject.register_observer(BorrowingObserver);

        let msg = String::from("Hello, Borrowing Observer!");
        subject.notify_observers(&msg);
    }
}