use c20_distributed::*;

struct DummyPing;
impl SwimTransport for DummyPing { fn ping(&self, _to: &str) -> bool { true } }

#[test]
fn swim_probe_alive() {
    let node = swim::SwimNode { node_id: "n0".into(), transport: DummyPing };
    let ev = node.probe("n1");
    assert_eq!(ev.state, swim::SwimMemberState::Alive);
}

#[test]
fn majority_quorum_rules() {
    assert_eq!(replication::MajorityQuorum::required_acks(3, ConsistencyLevel::Quorum), 2);
    assert_eq!(replication::MajorityQuorum::required_acks(5, ConsistencyLevel::Strong), 3);
    assert_eq!(replication::MajorityQuorum::required_acks(4, ConsistencyLevel::Eventual), 1);
}

