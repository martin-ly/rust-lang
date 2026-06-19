//! # 练习 6: 多线程链接检查器 / Exercise 6: Multi-threaded Link Checker
//!
//! **难度 / Difficulty**: Hard  
//! **考点 / Focus**: Threads、Channels、Arc、错误处理
//!
//! ## 题目描述 / Problem Description
//!
//! 实现一个多线程链接检查器。输入一组 URL，使用多个工作线程并发检查，
//! 主线程收集结果并返回每个 URL 的状态。
//!
//! 对应 Google Comprehensive Rust Concurrency 专题练习：Multi-threaded Link Checker。
//!
//! ## 要求 / Requirements
//!
//! - 使用 `std::thread` 和 `std::sync::mpsc` 实现
//! - 工作线程数量可配置
//! - 不得使用 `unsafe` / Do not use `unsafe`

use std::collections::HashMap;
use std::sync::mpsc::{Sender, channel};
use std::sync::{Arc, Mutex};
use std::thread;

/// 链接检查结果
/// Result of checking a single link
#[derive(Debug, Clone, PartialEq)]
pub enum LinkStatus {
    Ok,
    Failed(String),
}

/// 多线程链接检查器
/// Multi-threaded link checker
pub struct LinkChecker;

impl LinkChecker {
    /// 并发检查多个链接
    ///
    /// - `urls`: 待检查的 URL 列表
    /// - `worker_count`: 工作线程数量
    /// - `fetch`: 模拟获取函数，返回 `Ok(())` 或 `Err(String)`
    pub fn check<F>(urls: &[String], worker_count: usize, fetch: F) -> HashMap<String, LinkStatus>
    where
        F: Fn(&str) -> Result<(), String> + Send + Sync + 'static,
    {
        if urls.is_empty() {
            return HashMap::new();
        }

        let fetch = Arc::new(fetch);
        let (tx, rx) = channel::<(String, LinkStatus)>();
        let url_queue = Arc::new(Mutex::new(urls.to_vec()));

        let mut handles = Vec::new();
        for _ in 0..worker_count {
            let tx: Sender<(String, LinkStatus)> = tx.clone();
            let queue = Arc::clone(&url_queue);
            let fetch = Arc::clone(&fetch);

            let handle = thread::spawn(move || {
                loop {
                    let url = {
                        let mut q = queue.lock().unwrap();
                        q.pop()
                    };

                    match url {
                        Some(url) => {
                            let status = match fetch(&url) {
                                Ok(()) => LinkStatus::Ok,
                                Err(e) => LinkStatus::Failed(e),
                            };
                            // 忽略发送失败（接收端可能已关闭）
                            let _ = tx.send((url, status));
                        }
                        None => break,
                    }
                }
            });
            handles.push(handle);
        }

        // 关闭发送端原始引用，只保留工作线程克隆
        drop(tx);

        let mut results = HashMap::new();
        for (url, status) in rx {
            results.insert(url, status);
        }

        for handle in handles {
            handle.join().expect("worker thread should not panic");
        }

        results
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mock_fetch(url: &str) -> Result<(), String> {
        if url.starts_with("https://ok.") {
            Ok(())
        } else {
            Err(format!("mock error for {}", url))
        }
    }

    #[test]
    fn test_check_multiple_links() {
        let urls: Vec<String> = (0..10)
            .map(|i| {
                if i % 2 == 0 {
                    format!("https://ok.site/{}", i)
                } else {
                    format!("https://fail.site/{}", i)
                }
            })
            .collect();

        let results = LinkChecker::check(&urls, 4, mock_fetch);

        assert_eq!(results.len(), 10);
        for i in 0..10 {
            let url = if i % 2 == 0 {
                format!("https://ok.site/{}", i)
            } else {
                format!("https://fail.site/{}", i)
            };
            let status = results.get(&url).expect("missing result");
            if i % 2 == 0 {
                assert_eq!(*status, LinkStatus::Ok);
            } else {
                assert!(matches!(status, LinkStatus::Failed(_)));
            }
        }
    }

    #[test]
    fn test_empty_urls() {
        let results: HashMap<String, LinkStatus> = LinkChecker::check(&[], 2, mock_fetch);
        assert!(results.is_empty());
    }

    #[test]
    fn test_single_worker() {
        let urls = vec!["https://ok.site/1".to_string()];
        let results = LinkChecker::check(&urls, 1, mock_fetch);
        assert_eq!(results.get("https://ok.site/1"), Some(&LinkStatus::Ok));
    }
}
