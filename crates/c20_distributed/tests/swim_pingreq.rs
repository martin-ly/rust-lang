use c20_distributed::swim::{SwimNode, SwimTransport, SwimMemberState};

struct StubTransport { fail_direct: bool, indirect_ok: bool }
impl SwimTransport for StubTransport {
    fn ping(&self, _to: &str) -> bool { !self.fail_direct }
    fn ping_req(&self, _relay: &str, _target: &str) -> bool { self.indirect_ok }
}

#[test]
fn indirect_probe_can_rescue() {
    let node = SwimNode { node_id: "n0".into(), transport: StubTransport { fail_direct: true, indirect_ok: true } };
    let ev = node.probe_indirect("n1", ["n2", "n3"].iter().copied());
    assert_eq!(ev.state, SwimMemberState::Alive);
}

