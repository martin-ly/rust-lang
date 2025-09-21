//! # 字符串算法模块
//! 
//! 本模块实现了各种字符串算法。

//use serde::{Serialize, Deserialize};

/// 字符串算法实现
pub struct StringAlgorithms;

impl StringAlgorithms {
    /// KMP 字符串匹配
    pub fn kmp_search(text: &str, pattern: &str) -> Option<usize> {
        let text_bytes = text.as_bytes();
        let pattern_bytes = pattern.as_bytes();
        
        if pattern_bytes.is_empty() {
            return Some(0);
        }
        
        let lps = Self::compute_lps(pattern_bytes);
        let mut i = 0;
        let mut j = 0;
        
        while i < text_bytes.len() {
            if text_bytes[i] == pattern_bytes[j] {
                i += 1;
                j += 1;
                
                if j == pattern_bytes.len() {
                    return Some(i - j);
                }
            } else if j > 0 {
                j = lps[j - 1];
            } else {
                i += 1;
            }
        }
        
        None
    }
    
    fn compute_lps(pattern: &[u8]) -> Vec<usize> {
        let mut lps = vec![0; pattern.len()];
        let mut len = 0;
        let mut i = 1;
        
        while i < pattern.len() {
            if pattern[i] == pattern[len] {
                len += 1;
                lps[i] = len;
                i += 1;
            } else if len > 0 {
                len = lps[len - 1];
            } else {
                lps[i] = 0;
                i += 1;
            }
        }
        
        lps
    }

    /// Rabin-Karp 字符串匹配
    pub fn rabin_karp_search(text: &str, pattern: &str) -> Option<usize> {
        let text_bytes = text.as_bytes();
        let pattern_bytes = pattern.as_bytes();
        
        if pattern_bytes.is_empty() {
            return Some(0);
        }
        
        if pattern_bytes.len() > text_bytes.len() {
            return None;
        }
        
        let base: u64 = 256;
        let modulus = 101;
        
        let mut pattern_hash = 0;
        let mut text_hash = 0;
        let mut h = 1;
        
        for _i in 0..pattern_bytes.len() - 1 {
            h = (h * base) % modulus;
        }
        
        for i in 0..pattern_bytes.len() {
            pattern_hash = (base * pattern_hash + pattern_bytes[i] as u64) % modulus;
            text_hash = (base * text_hash + text_bytes[i] as u64) % modulus;
        }
        
        for i in 0..=text_bytes.len() - pattern_bytes.len() {
            if pattern_hash == text_hash {
                let mut j = 0;
                while j < pattern_bytes.len() && text_bytes[i + j] == pattern_bytes[j] {
                    j += 1;
                }
                if j == pattern_bytes.len() {
                    return Some(i);
                }
            }
            
            if i < text_bytes.len() - pattern_bytes.len() {
                // 更新滚动哈希值，避免负值问题
                let old_char_value = text_bytes[i] as u64;
                let new_char_value = text_bytes[i + pattern_bytes.len()] as u64;
                
                // 移除最左边的字符并添加最右边的字符
                text_hash = (base * (text_hash + modulus - (old_char_value * h) % modulus) + new_char_value) % modulus;
            }
        }
        
        None
    }
}
