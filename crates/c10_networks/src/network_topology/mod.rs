//! 网络拓扑与路由发现（教学化简化版）

use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NodeId(pub String);

#[derive(Debug, Clone)]
pub struct Edge { pub from: NodeId, pub to: NodeId, pub weight: u32 }

#[derive(Debug, Default)]
pub struct TopologyGraph {
    pub nodes: HashSet<NodeId>,
    pub adj: HashMap<NodeId, Vec<Edge>>,
}

impl TopologyGraph {
    pub fn new() -> Self { Self::default() }
    pub fn add_node(&mut self, id: NodeId) { self.nodes.insert(id); }
    pub fn add_edge(&mut self, from: NodeId, to: NodeId, weight: u32) {
        self.nodes.insert(from.clone());
        self.nodes.insert(to.clone());
        self.adj.entry(from.clone()).or_default().push(Edge{ from, to, weight });
    }

    /// 简化版 BFS 路由发现
    pub fn find_path_bfs(&self, src: &NodeId, dst: &NodeId) -> Option<Vec<NodeId>> {
        let mut q = VecDeque::new();
        let mut prev: HashMap<NodeId, NodeId> = HashMap::new();
        let mut seen: HashSet<NodeId> = HashSet::new();
        q.push_back(src.clone());
        seen.insert(src.clone());
        while let Some(n) = q.pop_front() {
            if &n == dst { break; }
            if let Some(edges) = self.adj.get(&n) {
                for e in edges {
                    if !seen.contains(&e.to) {
                        seen.insert(e.to.clone());
                        prev.insert(e.to.clone(), n.clone());
                        q.push_back(e.to.clone());
                    }
                }
            }
        }
        if !seen.contains(dst) { return None; }
        let mut path = vec![dst.clone()];
        let mut cur = dst.clone();
        while let Some(p) = prev.get(&cur).cloned() {
            path.push(p.clone());
            if &p == src { break; }
            cur = p;
        }
        path.reverse();
        Some(path)
    }
}


