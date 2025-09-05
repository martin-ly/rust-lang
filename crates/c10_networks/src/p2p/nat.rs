//! NAT 可达性与端口映射抽象（预留接口）

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reachability {
    Public,
    NatRestricted,
    Unknown,
}

pub trait NatTraversal {
    fn detect(&self) -> Reachability;
}


