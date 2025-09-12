use proptest::prelude::*;
use c20_distributed::swim::{SwimNode, SwimTransport, SwimMemberState, MembershipView};

#[derive(Clone, Default)]
struct MockTrans { reachable: std::collections::HashMap<String, bool> }

impl SwimTransport for MockTrans {
    fn ping(&self, to: &str) -> bool { *self.reachable.get(to).unwrap_or(&true) }
}

proptest! {
    #[test]
    fn direct_probe_reflects_reachability(name in "[a-z]{1,4}", ok in any::<bool>()) {
        let mut t = MockTrans::default();
        t.reachable.insert(name.clone(), ok);
        let node = SwimNode { node_id: "me".to_string(), transport: t, probe_interval_ms: 0, fanout: 1 };
        let ev = node.probe(&name);
        prop_assert_eq!(ev.node_id, name);
        prop_assert_eq!(ev.state, if ok { SwimMemberState::Alive } else { SwimMemberState::Suspect });
    }
}

proptest! {
    #[test]
    fn membership_merge_respects_version(moniker in "[a-z]{1,4}") {
        use c20_distributed::swim::{MemberInfo, Version};
        let mut a = MembershipView::new("me".to_string());
        let mut b = MembershipView::new("me".to_string());
        a.local_update(&moniker, SwimMemberState::Alive);
        // b 比 a 新
        b.members.insert(moniker.clone(), MemberInfo { state: SwimMemberState::Faulty, version: Version(10) });
        a.merge_from(&[(moniker.clone(), b.members.get(&moniker).unwrap().clone())]);
        prop_assert_eq!(a.members.get(&moniker).unwrap().state, SwimMemberState::Faulty);
    }
}


