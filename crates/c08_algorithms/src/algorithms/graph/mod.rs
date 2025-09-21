//! # 图算法模块
//! 
//! 本模块实现了各种图算法。

use serde::{Serialize, Deserialize};
use std::collections::{
    //HashMap,
    VecDeque,
};

/// 图结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Graph {
    pub vertices: usize,
    pub edges: Vec<(usize, usize, f64)>, // (from, to, weight)
}

/// 图算法结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum GraphResult {
    Distances(Vec<f64>),
    Path(Vec<usize>),
    Boolean(bool),
}

/// 图算法实现
pub struct GraphAlgorithms;

impl GraphAlgorithms {
    /// BFS 搜索
    pub fn bfs(graph: &Graph, start: usize) -> GraphResult {
        let mut visited = vec![false; graph.vertices];
        let mut queue = VecDeque::new();
        let mut distances = vec![f64::INFINITY; graph.vertices];
        
        visited[start] = true;
        distances[start] = 0.0;
        queue.push_back(start);
        
        while let Some(current) = queue.pop_front() {
            for &(from, to, weight) in &graph.edges {
                if from == current && !visited[to] {
                    visited[to] = true;
                    distances[to] = distances[current] + weight;
                    queue.push_back(to);
                }
            }
        }
        
        GraphResult::Distances(distances)
    }

    /// DFS 搜索
    pub fn dfs(graph: &Graph, start: usize) -> GraphResult {
        let mut visited = vec![false; graph.vertices];
        let mut path = Vec::new();
        
        Self::dfs_recursive(graph, start, &mut visited, &mut path);
        
        GraphResult::Path(path)
    }
    
    fn dfs_recursive(graph: &Graph, current: usize, visited: &mut [bool], path: &mut Vec<usize>) {
        visited[current] = true;
        path.push(current);
        
        for &(from, to, _) in &graph.edges {
            if from == current && !visited[to] {
                Self::dfs_recursive(graph, to, visited, path);
            }
        }
    }
}
