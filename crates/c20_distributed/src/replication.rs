use crate::consistency::ConsistencyLevel;
use crate::errors::DistributedError;
use crate::topology::ConsistentHashRing;
use crate::storage::IdempotencyStore;

pub trait Replicator<C> {
    fn replicate(&mut self, command: C, level: ConsistencyLevel) -> Result<(), DistributedError>;
}

pub trait QuorumPolicy {
    fn required_acks(total: usize, level: ConsistencyLevel) -> usize;
}

pub struct MajorityQuorum;

impl QuorumPolicy for MajorityQuorum {
    fn required_acks(total: usize, level: ConsistencyLevel) -> usize {
        match level {
            ConsistencyLevel::Strong | ConsistencyLevel::Quorum => (total / 2) + 1,
            ConsistencyLevel::Eventual => 1,
        }
    }
}

use std::collections::HashMap;

pub struct LocalReplicator<ID> {
    pub ring: ConsistentHashRing,
    pub nodes: Vec<String>,
    pub successes: HashMap<String, bool>,
    pub idempotency: Option<Box<dyn IdempotencyStore<ID> + Send>>, 
}

impl<ID> LocalReplicator<ID> {
    pub fn new(ring: ConsistentHashRing, nodes: Vec<String>) -> Self {
        Self { ring, nodes, successes: HashMap::new(), idempotency: None }
    }

    pub fn with_idempotency(mut self, store: Box<dyn IdempotencyStore<ID> + Send>) -> Self {
        self.idempotency = Some(store);
        self
    }

    pub fn replicate_to_nodes<C: Clone>(&mut self, targets: &[String], _command: C, level: ConsistencyLevel) -> Result<(), DistributedError> {
        let total = targets.len();
        let need = MajorityQuorum::required_acks(total, level);
        let mut acks = 0usize;
        for n in targets {
            if *self.successes.get(n).unwrap_or(&true) {
                acks += 1;
            }
        }
        if acks >= need { Ok(()) } else { Err(DistributedError::Network(format!("acks {acks}/{need}"))) }
    }

    pub fn replicate_idempotent<C: Clone>(&mut self, id: &ID, targets: &[String], command: C, level: ConsistencyLevel) -> Result<(), DistributedError>
    where ID: Clone
    {
        if let Some(store) = &self.idempotency {
            if store.seen(id) {
                return Ok(());
            }
        }
        let res = self.replicate_to_nodes(targets, command, level);
        if res.is_ok() {
            if let Some(store) = &mut self.idempotency {
                store.record(id.clone());
            }
        }
        res
    }
}

impl<C: Clone, ID> Replicator<C> for LocalReplicator<ID> {
    fn replicate(&mut self, command: C, level: ConsistencyLevel) -> Result<(), DistributedError> {
        let nodes = self.nodes.clone();
        self.replicate_to_nodes(&nodes, command, level)
    }
}

