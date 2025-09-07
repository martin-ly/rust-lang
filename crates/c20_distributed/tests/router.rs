use c20_distributed::topology::ConsistentHashRing;
use c20_distributed::partitioning::HashRingRouter;

#[test]
fn route_owner_exists() {
    let mut ring = ConsistentHashRing::new(32);
    ring.add_node("n1");
    ring.add_node("n2");
    let router = HashRingRouter::new(ring);
    let owner = router.owner_of(&"k-01");
    assert!(owner.is_some());
}

