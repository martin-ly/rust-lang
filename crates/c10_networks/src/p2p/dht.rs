//! DHT 抽象（预留接口）

#[derive(Clone, Debug)]
pub struct DhtKey(pub Vec<u8>);

#[derive(Clone, Debug)]
pub struct DhtValue(pub Vec<u8>);

pub trait Dht {
    fn put(&mut self, key: &DhtKey, value: DhtValue);
    fn get(&self, key: &DhtKey) -> Option<DhtValue>;
}
