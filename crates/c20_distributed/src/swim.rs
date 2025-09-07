use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SwimMemberState {
    Alive,
    Suspect,
    Faulty,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SwimEvent {
    pub node_id: String,
    pub state: SwimMemberState,
}

pub trait SwimTransport {
    fn ping(&self, to: &str) -> bool;
    fn ping_req(&self, relay: &str, target: &str) -> bool { let _ = relay; self.ping(target) }
}

#[derive(Default)]
pub struct SwimNode<T: SwimTransport> {
    pub node_id: String,
    pub transport: T,
}

impl<T: SwimTransport> SwimNode<T> {
    pub fn probe(&self, peer: &str) -> SwimEvent {
        let ok = self.transport.ping(peer);
        SwimEvent { node_id: peer.to_string(), state: if ok { SwimMemberState::Alive } else { SwimMemberState::Suspect } }
    }

    pub fn probe_indirect<'a>(&self, target: &str, relays: impl IntoIterator<Item=&'a str>) -> SwimEvent {
        if self.transport.ping(target) {
            return SwimEvent { node_id: target.to_string(), state: SwimMemberState::Alive };
        }
        for r in relays {
            if self.transport.ping_req(r, target) {
                return SwimEvent { node_id: target.to_string(), state: SwimMemberState::Alive };
            }
        }
        SwimEvent { node_id: target.to_string(), state: SwimMemberState::Suspect }
    }
}

use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Version(pub u64);

#[derive(Debug, Clone)]
pub struct MemberInfo {
    pub state: SwimMemberState,
    pub version: Version,
}

#[derive(Default, Debug, Clone)]
pub struct MembershipView {
    pub me: String,
    pub members: HashMap<String, MemberInfo>,
}

impl MembershipView {
    pub fn new(me: String) -> Self { Self { me, members: HashMap::new() } }

    pub fn local_update(&mut self, node: &str, state: SwimMemberState) {
        let ent = self.members.entry(node.to_string()).or_insert(MemberInfo { state, version: Version(0) });
        ent.version.0 += 1;
        ent.state = state;
    }

    pub fn gossip_payload(&self) -> Vec<(String, MemberInfo)> {
        self.members.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }

    pub fn merge_from(&mut self, incoming: &[(String, MemberInfo)]) {
        for (node, info) in incoming {
            let ent = self.members.entry(node.clone()).or_insert(MemberInfo { state: info.state, version: info.version });
            if info.version.0 > ent.version.0 { *ent = info.clone(); }
        }
    }
}

