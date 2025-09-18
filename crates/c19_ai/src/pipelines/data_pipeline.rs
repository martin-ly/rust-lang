//! 数据管道草案模块：提供最小可组合接口，后续补充数据源/缓存/校验。

use std::time::Instant;

#[allow(dead_code)]
pub struct DataPipeline;

#[allow(dead_code)]
impl DataPipeline {
    pub fn new() -> Self {
        Self
    }

    /// 从输入数据构建最小数据批次并返回统计信息
    pub fn run_once<T: Clone>(&self, input: &[T]) -> (Vec<T>, usize) {
        let start = Instant::now();
        let batch: Vec<T> = input.to_vec();
        let _elapsed = start.elapsed();
        (batch, 1)
    }
}
