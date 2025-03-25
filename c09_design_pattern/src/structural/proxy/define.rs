// 定义一个 Subject trait
#[allow(unused)]
trait Subject {
    fn request(&self);
}

// 真实主题的实现
#[allow(unused)]
struct RealSubject;

impl Subject for RealSubject {
    fn request(&self) {
        println!("RealSubject: Handling request.");
    }
}

// 代理的实现
#[allow(unused)]
struct Proxy<T: Subject> {
    real_subject: T,
}

impl<T: Subject> Subject for Proxy<T> {
    fn request(&self) {
        println!("Proxy: Pre-processing before request.");
        self.real_subject.request();
        println!("Proxy: Post-processing after request.");
    }
}

// 使用示例
#[allow(unused)]
pub fn test_proxy() {
    let real_subject = RealSubject;
    let proxy = Proxy { real_subject };

    proxy.request();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proxy01() {
        test_proxy();
    }
}



