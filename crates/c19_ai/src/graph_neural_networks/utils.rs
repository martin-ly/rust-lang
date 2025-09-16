//! 图神经网络工具
//!
//! 提供图神经网络的辅助工具

use anyhow::Result;

/// 图神经网络工具
pub struct GNNUtils;

impl GNNUtils {
    /// 计算邻接矩阵
    pub fn compute_adjacency_matrix(
        edges: &[(usize, usize)],
        num_nodes: usize,
    ) -> Result<Vec<Vec<f32>>> {
        let mut adjacency = vec![vec![0.0; num_nodes]; num_nodes];

        for &(i, j) in edges {
            if i < num_nodes && j < num_nodes {
                adjacency[i][j] = 1.0;
                adjacency[j][i] = 1.0; // 无向图
            }
        }

        Ok(adjacency)
    }

    /// 计算度矩阵
    pub fn compute_degree_matrix(adjacency: &[Vec<f32>]) -> Result<Vec<Vec<f32>>> {
        let num_nodes = adjacency.len();
        let mut degree = vec![vec![0.0; num_nodes]; num_nodes];

        for i in 0..num_nodes {
            let degree_sum: f32 = adjacency[i].iter().sum();
            degree[i][i] = degree_sum;
        }

        Ok(degree)
    }
}
