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
    fn handle_append_entries(
        &mut self,
        req: AppendEntriesReq<E>,
    ) -> Result<AppendEntriesResp, DistributedError>;
    fn handle_request_vote(
        &mut self,
        req: RequestVoteReq,
    ) -> Result<RequestVoteResp, DistributedError>;
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
        Self {
            state: RaftState::Follower,
            term: Term(0),
            log: Vec::new(),
            commit_index: 0,
            last_applied: 0,
            apply: None,
        }
    }

    pub fn install_snapshot(&mut self) {
        // For minimal skeleton, snapshot just truncates log
        self.log.clear();
        self.commit_index = 0;
        self.last_applied = 0;
    }

    pub fn set_apply(&mut self, f: Box<dyn FnMut(&E) + Send>) {
        self.apply = Some(f);
    }

    /// 提供作用域内生效的 apply 回调，而不要求 'static。
    /// 使用方法：
    /// let mut guard = raft.set_apply_scoped(&mut apply_fn);
    /// guard.handle_append_entries(req)?;
    pub fn set_apply_scoped<'a>(
        &'a mut self,
        f: &'a mut (dyn FnMut(&E) + Send),
    ) -> ScopedApply<'a, E> {
        ScopedApply {
            raft: self,
            apply: f,
        }
    }

    /// 内部核心实现：可传入临时回调用于应用 entries
    fn handle_append_entries_core(
        &mut self,
        req: AppendEntriesReq<E>,
        mut apply: Option<&mut (dyn FnMut(&E) + Send)>,
    ) -> Result<AppendEntriesResp, DistributedError>
    where
        E: Clone,
    {
        if req.term.0 < self.term.0 {
            return Ok(AppendEntriesResp {
                term: self.term,
                success: false,
            });
        }
        if req.term.0 > self.term.0 {
            self.term = req.term;
        }
        self.state = RaftState::Follower;

        // prev check
        let prev_idx = req.prev_log_index.0 as usize;
        if prev_idx > 0 {
            let i = prev_idx - 1;
            if let Some((t, _)) = self.log.get(i) {
                if t.0 != req.prev_log_term.0 {
                    return Ok(AppendEntriesResp {
                        term: self.term,
                        success: false,
                    });
                }
            } else {
                return Ok(AppendEntriesResp {
                    term: self.term,
                    success: false,
                });
            }
        }

        // overwrite from prev_log_index
        let mut insert_at = prev_idx;
        if insert_at > self.log.len() {
            insert_at = self.log.len();
        }
        self.log.truncate(insert_at);
        for e in req.entries.into_iter() {
            self.log.push((self.term, e));
        }

        // commit & apply
        let leader_commit = req.leader_commit.0 as usize;
        let log_len = self.log.len();
        self.commit_index = std::cmp::min(leader_commit, log_len);
        while self.last_applied < self.commit_index {
            let idx = self.last_applied; // 0-based
            if let Some((_, entry)) = self.log.get(idx) {
                if let Some(ref mut cb) = apply {
                    (cb)(entry);
                }
            }
            self.last_applied += 1;
        }

        Ok(AppendEntriesResp {
            term: self.term,
            success: true,
        })
    }
}

impl<E: Clone> RaftNode<E> for MinimalRaft<E> {
    fn state(&self) -> RaftState {
        self.state
    }
    fn current_term(&self) -> Term {
        self.term
    }

    fn handle_append_entries(
        &mut self,
        req: AppendEntriesReq<E>,
    ) -> Result<AppendEntriesResp, DistributedError> {
        // 将已有的 'static 回调透传给核心实现（通过临时 take 避免可变别名）
        let mut taken = self.apply.take();
        let res = match taken.as_mut() {
            Some(cb) => self
                .handle_append_entries_core(req, Some(cb.as_mut() as &mut (dyn FnMut(&E) + Send))),
            None => self.handle_append_entries_core(req, None),
        };
        self.apply = taken;
        res
    }

    fn handle_request_vote(
        &mut self,
        req: RequestVoteReq,
    ) -> Result<RequestVoteResp, DistributedError> {
        if req.term.0 > self.term.0 {
            self.term = req.term;
            self.state = RaftState::Follower;
            return Ok(RequestVoteResp {
                term: self.term,
                vote_granted: true,
            });
        }
        Ok(RequestVoteResp {
            term: self.term,
            vote_granted: false,
        })
    }
}

/// 守卫式作用域对象：对 `MinimalRaft` 的操作将使用提供的非 'static 回调
pub struct ScopedApply<'a, E> {
    raft: &'a mut MinimalRaft<E>,
    apply: &'a mut (dyn FnMut(&E) + Send),
}

impl<'a, E> ScopedApply<'a, E> {
    pub fn inner(&mut self) -> &mut MinimalRaft<E> {
        self.raft
    }
}

impl<'a, E: Clone> RaftNode<E> for ScopedApply<'a, E> {
    fn state(&self) -> RaftState {
        self.raft.state()
    }
    fn current_term(&self) -> Term {
        self.raft.current_term()
    }
    fn handle_append_entries(
        &mut self,
        req: AppendEntriesReq<E>,
    ) -> Result<AppendEntriesResp, DistributedError> {
        self.raft.handle_append_entries_core(req, Some(self.apply))
    }
    fn handle_request_vote(
        &mut self,
        req: RequestVoteReq,
    ) -> Result<RequestVoteResp, DistributedError> {
        self.raft.handle_request_vote(req)
    }
}
