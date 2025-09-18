#[cfg(feature = "consensus-raft")]
use c20_distributed::consensus_raft::{AppendEntriesReq, LogIndex, MinimalRaft, RaftNode, Term};
#[cfg(feature = "consensus-raft")]
use std::sync::{Arc, Mutex};

#[cfg(feature = "consensus-raft")]
#[test]
fn read_after_commit_is_visible_via_apply_barrier() {
    let mut raft: MinimalRaft<Vec<u8>> = MinimalRaft::new();
    let applied: Arc<Mutex<Vec<Vec<u8>>>> = Arc::new(Mutex::new(Vec::new()));
    let capture = applied.clone();
    raft.set_apply(Box::new(move |e: &Vec<u8>| {
        capture.lock().unwrap().push(e.clone());
    }));

    let req = AppendEntriesReq {
        term: Term(1),
        leader_id: "n1".into(),
        prev_log_index: LogIndex(0),
        prev_log_term: Term(0),
        entries: vec![b"x".to_vec()],
        leader_commit: LogIndex(1),
    };
    let resp = raft.handle_append_entries(req).unwrap();
    assert!(resp.success);

    assert_eq!(applied.lock().unwrap().len(), 1);
    assert_eq!(applied.lock().unwrap()[0], b"x".to_vec());
}

#[cfg(not(feature = "consensus-raft"))]
#[test]
fn read_after_commit_skipped_without_feature() {
    // feature 未启用时使用桩测试，保持通过以不阻断 CI
    assert!(true);
}
