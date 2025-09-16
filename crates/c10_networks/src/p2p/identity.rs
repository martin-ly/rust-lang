//! 节点身份与密钥管理抽象

#[derive(Clone, Debug)]
pub struct NodeIdentity {
    pub peer_id_hex: String,
}

impl NodeIdentity {
    pub fn new(peer_id_hex: String) -> Self {
        Self { peer_id_hex }
    }
}
