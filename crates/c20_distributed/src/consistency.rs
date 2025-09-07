#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConsistencyLevel {
    Strong,
    Quorum,
    Eventual,
}

