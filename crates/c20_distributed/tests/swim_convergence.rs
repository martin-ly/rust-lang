use c20_distributed::swim::{MembershipView, SwimMemberState};

#[test]
fn swim_view_converges_on_higher_version() {
    let mut a = MembershipView::new("a".into());
    a.local_update("n1", SwimMemberState::Alive);
    let mut b = a.clone();
    b.local_update("n1", SwimMemberState::Suspect);
    let payload = b.gossip_payload();
    a.merge_from(&payload);
    let n1 = a.members.get("n1").unwrap();
    assert_eq!(n1.state, SwimMemberState::Suspect);
    assert!(n1.version.0 >= 2);
}
