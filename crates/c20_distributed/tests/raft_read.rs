#[cfg(feature = "consensus-raft")]
use c20_distributed::consensus_raft::{MinimalRaft, RaftNode, AppendEntriesReq, Term, LogIndex};

#[cfg(feature = "consensus-raft")]
#[test]
fn read_after_commit_is_visible_via_apply_barrier() {
    let mut raft: MinimalRaft<Vec<u8>> = MinimalRaft::new();
    let mut applied: Vec<Vec<u8>> = Vec::new();
    raft.set_apply(Box::new(|e: &Vec<u8>| applied.push(e.clone())));

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

    assert_eq!(applied.len(), 1);
    assert_eq!(applied[0], b"x".to_vec());
}

#[cfg(not(feature = "consensus-raft"))]
#[test]
fn read_after_commit_skipped_without_feature() {
    // feature 未启用时占位，保持测试通过
    assert!(true);
}
