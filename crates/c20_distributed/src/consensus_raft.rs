//! Raft 接口骨架（受 feature `consensus-raft` 门控）

use crate::errors::DistributedError;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RaftState {
    Follower,
    Candidate,
    Leader,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Term(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LogIndex(pub u64);

#[derive(Debug, Clone)]
pub struct AppendEntriesReq<E> {
    pub term: Term,
    pub leader_id: String,
    pub prev_log_index: LogIndex,
    pub prev_log_term: Term,
    pub entries: Vec<E>,
    pub leader_commit: LogIndex,
}

#[derive(Debug, Clone)]
pub struct AppendEntriesResp {
    pub term: Term,
    pub success: bool,
}

#[derive(Debug, Clone)]
pub struct RequestVoteReq {
    pub term: Term,
    pub candidate_id: String,
    pub last_log_index: LogIndex,
    pub last_log_term: Term,
}

#[derive(Debug, Clone)]
pub struct RequestVoteResp {
    pub term: Term,
    pub vote_granted: bool,
}

pub trait RaftNode<E> {
    fn state(&self) -> RaftState;
    fn current_term(&self) -> Term;
    fn handle_append_entries(&mut self, req: AppendEntriesReq<E>) -> Result<AppendEntriesResp, DistributedError>;
    fn handle_request_vote(&mut self, req: RequestVoteReq) -> Result<RequestVoteResp, DistributedError>;
}

pub struct MinimalRaft<E> {
    state: RaftState,
    term: Term,
    log: Vec<(Term, E)>,
    commit_index: usize,
    last_applied: usize,
    apply: Option<Box<dyn FnMut(&E) + Send>>, 
}

impl<E> MinimalRaft<E> {
    pub fn new() -> Self {
        Self { state: RaftState::Follower, term: Term(0), log: Vec::new(), commit_index: 0, last_applied: 0, apply: None }
    }

    pub fn install_snapshot(&mut self) {
        // For minimal skeleton, snapshot just truncates log
        self.log.clear();
        self.commit_index = 0;
        self.last_applied = 0;
    }

    pub fn set_apply(&mut self, f: Box<dyn FnMut(&E) + Send>) { self.apply = Some(f); }
}

impl<E: Clone> RaftNode<E> for MinimalRaft<E> {
    fn state(&self) -> RaftState { self.state }
    fn current_term(&self) -> Term { self.term }

    fn handle_append_entries(&mut self, req: AppendEntriesReq<E>) -> Result<AppendEntriesResp, DistributedError> {
        if req.term.0 < self.term.0 {
            return Ok(AppendEntriesResp { term: self.term, success: false });
        }
        // Step down if term is newer
        if req.term.0 > self.term.0 { self.term = req.term; }
        self.state = RaftState::Follower;

        // prev check
        let prev_idx = req.prev_log_index.0 as usize;
        if prev_idx > 0 {
            // log indices are 1-based in Raft; our vec is 0-based
            let i = prev_idx - 1;
            if let Some((t, _)) = self.log.get(i) {
                if t.0 != req.prev_log_term.0 {
                    return Ok(AppendEntriesResp { term: self.term, success: false });
                }
            } else {
                return Ok(AppendEntriesResp { term: self.term, success: false });
            }
        }

        // append entries, overwriting conflicts from prev_log_index
        let mut insert_at = prev_idx;
        if insert_at > self.log.len() { insert_at = self.log.len(); }
        // truncate
        self.log.truncate(insert_at);
        for e in req.entries.into_iter() {
            self.log.push((self.term, e));
        }

        // update commit index and apply
        let leader_commit = req.leader_commit.0 as usize;
        let log_len = self.log.len();
        self.commit_index = std::cmp::min(leader_commit, log_len);
        while self.last_applied < self.commit_index {
            let idx = self.last_applied; // 0-based
            if let Some((_, entry)) = self.log.get(idx) {
                if let Some(ref mut apply) = self.apply { (apply)(entry); }
            }
            self.last_applied += 1;
        }

        Ok(AppendEntriesResp { term: self.term, success: true })
    }

    fn handle_request_vote(&mut self, req: RequestVoteReq) -> Result<RequestVoteResp, DistributedError> {
        if req.term.0 > self.term.0 {
            self.term = req.term;
            self.state = RaftState::Follower;
            return Ok(RequestVoteResp { term: self.term, vote_granted: true });
        }
        Ok(RequestVoteResp { term: self.term, vote_granted: false })
    }
}

