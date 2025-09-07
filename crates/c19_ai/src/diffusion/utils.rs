//! 扩散模型工具
//! 
//! 提供扩散模型的辅助工具

use anyhow::Result;

/// 扩散模型工具
pub struct DiffusionUtils;

impl DiffusionUtils {
    /// 计算噪声调度
    pub fn compute_noise_schedule(num_steps: usize) -> Vec<f32> {
        (0..num_steps)
            .map(|i| i as f32 / num_steps as f32)
            .collect()
    }
    
    /// 添加噪声
    pub fn add_noise(signal: &[f32], noise: &[f32], alpha: f32) -> Result<Vec<f32>> {
        if signal.len() != noise.len() {
            return Err(anyhow::anyhow!("信号和噪声长度不匹配"));
        }
        
        Ok(signal
            .iter()
            .zip(noise.iter())
            .map(|(s, n)| alpha * s + (1.0 - alpha) * n)
            .collect())
    }
}
