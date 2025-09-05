//! 发布订阅抽象（预留接口）

pub trait PubSub {
    fn join(&mut self, topic: &str);
    fn publish(&mut self, topic: &str, data: &[u8]);
}


