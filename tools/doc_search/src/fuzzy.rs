// 模糊搜索和正则表达式搜索模块

use fuzzy_matcher::FuzzyMatcher;
use fuzzy_matcher::skim::SkimMatcherV2;
use regex::Regex;

/// 模糊匹配器
pub struct FuzzySearcher {
    matcher: SkimMatcherV2,
    threshold: f64,
}

impl FuzzySearcher {
    /// 创建新的模糊搜索器
    pub fn new(threshold: f64) -> Self {
        Self {
            matcher: SkimMatcherV2::default(),
            threshold,
        }
    }
    
    /// 模糊匹配
    pub fn fuzzy_match(&self, query: &str, text: &str) -> Option<f64> {
        self.matcher.fuzzy_match(text, query).map(|score| {
            // 归一化分数到 0-1
            let normalized = score as f64 / 100.0;
            if normalized >= self.threshold {
                Some(normalized)
            } else {
                None
            }
        }).flatten()
    }
    
    /// 批量模糊匹配
    pub fn fuzzy_match_lines(&self, query: &str, lines: &[String]) -> Vec<(usize, f64)> {
        lines
            .iter()
            .enumerate()
            .filter_map(|(i, line)| {
                self.fuzzy_match(query, line).map(|score| (i, score))
            })
            .collect()
    }
}

/// 正则表达式搜索器
pub struct RegexSearcher {
    regex: Regex,
}

impl RegexSearcher {
    /// 创建新的正则搜索器
    pub fn new(pattern: &str) -> Result<Self, regex::Error> {
        let regex = Regex::new(pattern)?;
        Ok(Self { regex })
    }
    
    /// 在文本中查找匹配
    pub fn find_matches(&self, text: &str) -> Vec<regex::Match> {
        self.regex.find_iter(text).collect()
    }
    
    /// 在多行文本中查找匹配
    pub fn find_in_lines(&self, lines: &[String]) -> Vec<(usize, Vec<regex::Match>)> {
        lines
            .iter()
            .enumerate()
            .filter_map(|(i, line)| {
                let matches: Vec<_> = self.regex.find_iter(line).collect();
                if matches.is_empty() {
                    None
                } else {
                    Some((i, matches))
                }
            })
            .collect()
    }
}

/// 搜索模式
pub enum SearchPattern {
    /// 普通文本搜索
    Plain(String),
    /// 正则表达式搜索
    Regex(RegexSearcher),
    /// 模糊搜索
    Fuzzy(String),
}

impl SearchPattern {
    /// 从字符串创建搜索模式
    pub fn from_string(query: &str, use_regex: bool, use_fuzzy: bool) -> Result<Self, regex::Error> {
        if use_regex {
            Ok(SearchPattern::Regex(RegexSearcher::new(query)?))
        } else if use_fuzzy {
            Ok(SearchPattern::Fuzzy(query.to_string()))
        } else {
            Ok(SearchPattern::Plain(query.to_string()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_fuzzy_match() {
        let searcher = FuzzySearcher::new(0.5);
        let score = searcher.fuzzy_match("rust", "rust programming");
        assert!(score.is_some());
    }
    
    #[test]
    fn test_regex_search() {
        let searcher = RegexSearcher::new(r"\brust\b").unwrap();
        let matches = searcher.find_matches("rust is great for rust programming");
        assert_eq!(matches.len(), 2);
    }
    
    #[test]
    fn test_fuzzy_match_lines() {
        let searcher = FuzzySearcher::new(0.5);
        let lines = vec![
            "Rust ownership".to_string(),
            "Python programming".to_string(),
            "Rust borrowing".to_string(),
        ];
        let matches = searcher.fuzzy_match_lines("rust", &lines);
        assert_eq!(matches.len(), 2);
    }
}

