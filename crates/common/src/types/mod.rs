//! 公共类型模块
//! 
//! 提供跨 crate 共享的基础类型定义。

use std::collections::HashMap;
use std::sync::Arc;

/// 线程安全的共享字符串
pub type SharedString = Arc<str>;

/// 共享字节向量
pub type SharedBytes = Arc<[u8]>;

/// 通用配置映射
pub type ConfigMap = HashMap<String, String>;

/// 版本信息结构
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Version {
    major: u32,
    minor: u32,
    patch: u32,
    pre_release: Option<String>,
}

impl Version {
    /// 创建新版本
    pub const fn new(major: u32, minor: u32, patch: u32) -> Self {
        Self {
            major,
            minor,
            patch,
            pre_release: None,
        }
    }
    
    /// 创建预发布版本
    pub fn pre_release(mut self, pre: impl Into<String>) -> Self {
        self.pre_release = Some(pre.into());
        self
    }
    
    /// 获取主版本号
    pub const fn major(&self) -> u32 {
        self.major
    }
    
    /// 获取次版本号
    pub const fn minor(&self) -> u32 {
        self.minor
    }
    
    /// 获取修订版本号
    pub const fn patch(&self) -> u32 {
        self.patch
    }
}

impl std::fmt::Display for Version {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)?;
        if let Some(pre) = &self.pre_release {
            write!(f, "-{}", pre)?;
        }
        Ok(())
    }
}

impl Default for Version {
    fn default() -> Self {
        Self::new(0, 1, 0)
    }
}

/// 带时间戳的数据
#[derive(Debug, Clone)]
pub struct Timestamped<T> {
    data: T,
    created_at: std::time::Instant,
}

impl<T> Timestamped<T> {
    /// 创建带时间戳的数据
    pub fn new(data: T) -> Self {
        Self {
            data,
            created_at: std::time::Instant::now(),
        }
    }
    
    /// 获取数据
    pub fn data(&self) -> &T {
        &self.data
    }
    
    /// 获取创建时间
    pub fn created_at(&self) -> std::time::Instant {
        self.created_at
    }
    
    /// 获取已过去的时间
    pub fn elapsed(&self) -> std::time::Duration {
        self.created_at.elapsed()
    }
    
    /// 解包数据
    pub fn into_inner(self) -> T {
        self.data
    }
    
    /// 映射数据
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Timestamped<U> {
        Timestamped {
            data: f(self.data),
            created_at: self.created_at,
        }
    }
}

/// 带元数据的数据包装
#[derive(Debug, Clone)]
pub struct Metadata<T> {
    data: T,
    meta: ConfigMap,
}

impl<T> Metadata<T> {
    /// 创建带元数据的数据
    pub fn new(data: T) -> Self {
        Self {
            data,
            meta: ConfigMap::new(),
        }
    }
    
    /// 获取数据
    pub fn data(&self) -> &T {
        &self.data
    }
    
    /// 获取可变数据
    pub fn data_mut(&mut self) -> &mut T {
        &mut self.data
    }
    
    /// 获取元数据
    pub fn meta(&self) -> &ConfigMap {
        &self.meta
    }
    
    /// 获取可变元数据
    pub fn meta_mut(&mut self) -> &mut ConfigMap {
        &mut self.meta
    }
    
    /// 插入元数据
    pub fn with_meta(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.meta.insert(key.into(), value.into());
        self
    }
    
    /// 解包数据
    pub fn into_inner(self) -> T {
        self.data
    }
}

/// 分页参数
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pagination {
    page: usize,
    per_page: usize,
}

impl Pagination {
    /// 默认每页数量
    pub const DEFAULT_PER_PAGE: usize = 20;
    /// 最大每页数量
    pub const MAX_PER_PAGE: usize = 100;
    
    /// 创建分页参数
    pub fn new(page: usize, per_page: usize) -> Self {
        Self {
            page: page.max(1),
            per_page: per_page.clamp(1, Self::MAX_PER_PAGE),
        }
    }
    
    /// 获取页码
    pub fn page(&self) -> usize {
        self.page
    }
    
    /// 获取每页数量
    pub fn per_page(&self) -> usize {
        self.per_page
    }
    
    /// 获取偏移量
    pub fn offset(&self) -> usize {
        (self.page - 1) * self.per_page
    }
    
    /// 下一页
    pub fn next(&self) -> Self {
        Self::new(self.page + 1, self.per_page)
    }
    
    /// 上一页
    pub fn prev(&self) -> Self {
        Self::new(self.page.saturating_sub(1).max(1), self.per_page)
    }
}

impl Default for Pagination {
    fn default() -> Self {
        Self::new(1, Self::DEFAULT_PER_PAGE)
    }
}

/// 分页结果
#[derive(Debug, Clone)]
pub struct Paginated<T> {
    items: Vec<T>,
    total: usize,
    pagination: Pagination,
}

impl<T> Paginated<T> {
    /// 创建分页结果
    pub fn new(items: Vec<T>, total: usize, pagination: Pagination) -> Self {
        Self {
            items,
            total,
            pagination,
        }
    }
    
    /// 获取项目
    pub fn items(&self) -> &[T] {
        &self.items
    }
    
    /// 获取总数
    pub fn total(&self) -> usize {
        self.total
    }
    
    /// 获取分页参数
    pub fn pagination(&self) -> &Pagination {
        &self.pagination
    }
    
    /// 获取总页数
    pub fn total_pages(&self) -> usize {
        (self.total + self.pagination.per_page - 1) / self.pagination.per_page
    }
    
    /// 是否有下一页
    pub fn has_next(&self) -> bool {
        self.pagination.page < self.total_pages()
    }
    
    /// 是否有上一页
    pub fn has_prev(&self) -> bool {
        self.pagination.page > 1
    }
    
    /// 映射数据
    pub fn map<U>(self, f: impl FnMut(T) -> U) -> Paginated<U> {
        Paginated {
            items: self.items.into_iter().map(f).collect(),
            total: self.total,
            pagination: self.pagination,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_version() {
        let v = Version::new(1, 2, 3);
        assert_eq!(v.to_string(), "1.2.3");
        
        let v = Version::new(1, 0, 0).pre_release("alpha");
        assert_eq!(v.to_string(), "1.0.0-alpha");
    }
    
    #[test]
    fn test_pagination() {
        let p = Pagination::new(2, 10);
        assert_eq!(p.offset(), 10);
        assert_eq!(p.next().page(), 3);
        assert_eq!(p.prev().page(), 1);
    }
    
    #[test]
    fn test_paginated() {
        let items: Vec<i32> = vec![1, 2, 3];
        let p = Pagination::new(1, 10);
        let result = Paginated::new(items, 100, p);
        
        assert_eq!(result.total(), 100);
        assert_eq!(result.total_pages(), 10);
        assert!(result.has_next());
        assert!(!result.has_prev());
    }
}
