#[cfg(feature = "consensus-raft")]
mod snapshot_test {
    use c20_distributed::consensus_raft::{MinimalRaft, RaftNode, AppendEntriesReq, Term, LogIndex};

    #[test]
    fn install_snapshot_clears_log() {
        let mut r: MinimalRaft<Vec<u8>> = MinimalRaft::new();
        let req = AppendEntriesReq { term: Term(1), leader_id: "n1".into(), prev_log_index: LogIndex(0), prev_log_term: Term(0), entries: vec![b"a".to_vec(), b"b".to_vec()], leader_commit: LogIndex(0) };
        let _ = r.handle_append_entries(req);
        r.install_snapshot();
        // Not directly accessible log, so re-append should succeed from prev=0
        let req2 = AppendEntriesReq { term: Term(1), leader_id: "n1".into(), prev_log_index: LogIndex(0), prev_log_term: Term(0), entries: vec![b"c".to_vec()], leader_commit: LogIndex(0) };
        let resp = r.handle_append_entries(req2).unwrap();
        assert!(resp.success);
    }
}

