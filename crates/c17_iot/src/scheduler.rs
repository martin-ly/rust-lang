//! # IoT 调度器模块 / IoT Scheduler Module
//!
//! 本模块实现了 IoT 系统的任务调度功能。
//! This module implements task scheduling functionality for IoT systems.

// use crate::types::*;
use std::collections::HashMap;

/// IoT 任务调度器 / IoT Task Scheduler
#[allow(unused)]
pub struct IoTScheduler {
    tasks: Vec<Task>,
    priorities: HashMap<String, u8>,
}

impl IoTScheduler {
    pub fn new() -> Self {
        Self {
            tasks: Vec::new(),
            priorities: HashMap::new(),
        }
    }

    pub fn add_task(&mut self, task: Task) {
        self.tasks.push(task);
    }

    /// 基本：按添加顺序返回 / FIFO
    pub fn schedule(&mut self) -> Vec<Task> {
        self.tasks.clone()
    }

    /// 按优先级从高到低（数值小优先）排序返回 / Priority order
    pub fn schedule_by_priority(&self) -> Vec<Task> {
        let mut v = self.tasks.clone();
        v.sort_by_key(|t| t.priority);
        v
    }

    /// 最早截止时间优先（EDF）/ Earliest Deadline First
    pub fn schedule_edf(&self) -> Vec<Task> {
        let mut v = self.tasks.clone();
        v.sort_by_key(|t| t.deadline);
        v
    }
}

/// 任务 / Task
#[derive(Debug, Clone)]
pub struct Task {
    pub id: String,
    pub name: String,
    pub priority: u8,
    pub deadline: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_priority_order() {
        let mut s = IoTScheduler::new();
        s.add_task(Task {
            id: "1".into(),
            name: "a".into(),
            priority: 5,
            deadline: 100,
        });
        s.add_task(Task {
            id: "2".into(),
            name: "b".into(),
            priority: 1,
            deadline: 200,
        });
        let v = s.schedule_by_priority();
        assert_eq!(v.first().unwrap().id, "2");
    }

    #[test]
    fn test_edf_order() {
        let mut s = IoTScheduler::new();
        s.add_task(Task {
            id: "1".into(),
            name: "a".into(),
            priority: 5,
            deadline: 300,
        });
        s.add_task(Task {
            id: "2".into(),
            name: "b".into(),
            priority: 1,
            deadline: 100,
        });
        let v = s.schedule_edf();
        assert_eq!(v.first().unwrap().id, "2");
    }
}
