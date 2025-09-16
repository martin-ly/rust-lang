//! 节点发现抽象（预留接口）

#[derive(Clone, Debug)]
pub struct PeerInfo {
    pub id_hex: String,
    pub addresses: Vec<String>,
}

pub trait Discovery {
    fn bootstrap(&mut self, seeds: &[PeerInfo]);
    fn find_peer(&self, id_hex: &str) -> Option<PeerInfo>;
}
