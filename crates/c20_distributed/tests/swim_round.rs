use c20_distributed::swim::{SwimNode, SwimTransport, SwimMemberState, MembershipView};

struct T { ok: bool }
impl SwimTransport for T {
    fn ping(&self, _to: &str) -> bool { self.ok }
}

#[test]
fn one_round_events_basic() {
    let node = SwimNode { node_id: "n0".into(), transport: T { ok: true }, probe_interval_ms: 1000, fanout: 3 };
    let view = MembershipView::new("n0".into());
    let peers = vec!["n1".to_string(), "n2".to_string()];
    let evs = view.one_round_events(&node, peers);
    assert!(evs.iter().all(|e| e.state == SwimMemberState::Alive));
}


