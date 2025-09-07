//! 强化学习工具
//! 
//! 提供强化学习的辅助工具

use anyhow::Result;

/// 强化学习工具
pub struct RLUtils;

impl RLUtils {
    /// 计算折扣奖励
    pub fn compute_discounted_rewards(rewards: &[f32], gamma: f32) -> Vec<f32> {
        let mut discounted = vec![0.0; rewards.len()];
        let mut running_sum = 0.0;
        
        for (i, &reward) in rewards.iter().enumerate().rev() {
            running_sum = reward + gamma * running_sum;
            discounted[i] = running_sum;
        }
        
        discounted
    }
    
    /// 计算优势函数
    pub fn compute_advantages(values: &[f32], rewards: &[f32], gamma: f32) -> Result<Vec<f32>> {
        if values.len() != rewards.len() {
            return Err(anyhow::anyhow!("值和奖励长度不匹配"));
        }
        
        let mut advantages = Vec::new();
        for (i, (&value, &reward)) in values.iter().zip(rewards.iter()).enumerate() {
            let next_value = if i + 1 < values.len() { values[i + 1] } else { 0.0 };
            let advantage = reward + gamma * next_value - value;
            advantages.push(advantage);
        }
        
        Ok(advantages)
    }
}
