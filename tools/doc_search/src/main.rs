// 🔍 Rust 学习项目 - 智能文档搜索工具
// 版本: v1.1
// 创建日期: 2025-10-20
// 更新日期: 2025-10-20

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use serde::{Deserialize, Serialize};

/// 搜索结果项
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchResult {
    /// 文件路径
    pub file_path: String,
    /// 匹配行号
    pub line_number: usize,
    /// 匹配内容（上下文）
    pub context: String,
    /// 相关性分数
    pub relevance_score: f64,
    /// 文档类型
    pub doc_type: DocumentType,
    /// 模块名称
    pub module: String,
}

/// 文档类型
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum DocumentType {
    /// 📊 知识图谱
    KnowledgeGraph,
    /// 📐 多维矩阵
    ComparisonMatrix,
    /// 🗺️ 思维导图
    MindMap,
    /// 💻 实战示例
    Examples,
    /// 📋 增强报告
    Report,
    /// 📘 主文档
    MainDoc,
    /// 🎓 理论文档
    Theory,
}

/// 文档索引
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DocumentIndex {
    /// 文档路径到内容的映射
    pub documents: HashMap<String, DocumentContent>,
    /// 关键词索引
    pub keyword_index: HashMap<String, Vec<String>>,
    /// 模块索引
    pub module_index: HashMap<String, Vec<String>>,
}

/// 文档内容
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DocumentContent {
    pub path: String,
    pub doc_type: DocumentType,
    pub module: String,
    pub lines: Vec<String>,
    pub keywords: Vec<String>,
}

/// 智能文档搜索器
pub struct DocSearcher {
    index: DocumentIndex,
    config: Config,
}

impl DocSearcher {
    /// 创建新的搜索器并构建索引
    pub fn new(root_path: &Path) -> Result<Self, Box<dyn std::error::Error>> {
        let config = Config::load_or_default();
        Self::new_with_config(root_path, config)
    }
    
    /// 使用指定配置创建搜索器
    pub fn new_with_config(root_path: &Path, config: Config) -> Result<Self, Box<dyn std::error::Error>> {
        // 尝试从缓存加载索引
        let index = if config.incremental_index {
            if let Some(cache_path) = &config.cache_path.or_else(|| IndexCache::default_cache_path()) {
                if cache_path.exists() {
                    if let Ok(cache) = IndexCache::load(cache_path) {
                        if cache.is_valid() && cache.metadata.source_path == root_path {
                            println!("✅ 从缓存加载索引");
                            cache.index
                        } else {
                            Self::build_and_cache_index(root_path, cache_path)?
                        }
                    } else {
                        Self::build_and_cache_index(root_path, cache_path)?
                    }
                } else {
                    Self::build_and_cache_index(root_path, cache_path)?
                }
            } else {
                Self::build_index(root_path)?
            }
        } else {
            Self::build_index(root_path)?
        };
        
        Ok(Self { index, config })
    }
    
    /// 构建索引并缓存
    fn build_and_cache_index(root_path: &Path, cache_path: &Path) -> Result<DocumentIndex, Box<dyn std::error::Error>> {
        let index = Self::build_index(root_path)?;
        
        // 保存缓存
        let cache = IndexCache::new(index.clone(), root_path.to_path_buf());
        cache.save(cache_path)?;
        
        Ok(index)
    }

    /// 构建文档索引
    fn build_index(root_path: &Path) -> Result<DocumentIndex, Box<dyn std::error::Error>> {
        let mut documents = HashMap::new();
        let mut keyword_index = HashMap::new();
        let mut module_index = HashMap::new();

        // 遍历 crates 目录
        let crates_path = root_path.join("crates");
        if crates_path.exists() {
            for entry in fs::read_dir(&crates_path)? {
                let entry = entry?;
                let module_path = entry.path();
                
                if module_path.is_dir() {
                    let module_name = module_path
                        .file_name()
                        .unwrap()
                        .to_string_lossy()
                        .to_string();
                    
                    Self::index_module(&module_path, &module_name, &mut documents, &mut keyword_index, &mut module_index)?;
                }
            }
        }

        // 索引根目录文档
        Self::index_root_docs(root_path, &mut documents, &mut keyword_index)?;

        Ok(DocumentIndex {
            documents,
            keyword_index,
            module_index,
        })
    }

    /// 索引模块文档
    fn index_module(
        module_path: &Path,
        module_name: &str,
        documents: &mut HashMap<String, DocumentContent>,
        keyword_index: &mut HashMap<String, Vec<String>>,
        module_index: &mut HashMap<String, Vec<String>>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 索引 docs 目录
        let docs_paths = vec![
            module_path.join("docs"),
            module_path.join("docs/theory"),
            module_path.join("docs/theory_enhanced"),
        ];

        for docs_path in docs_paths {
            if docs_path.exists() {
                Self::index_directory(&docs_path, module_name, documents, keyword_index, module_index)?;
            }
        }

        // 索引模块根目录的 README 和报告
        for file_name in &["README.md", format!("{}_COMPREHENSIVE_ENHANCEMENT_REPORT_2025_10_20.md", module_name.to_uppercase())] {
            let file_path = module_path.join(file_name);
            if file_path.exists() {
                Self::index_file(&file_path, module_name, documents, keyword_index, module_index)?;
            }
        }

        Ok(())
    }

    /// 索引根目录文档
    fn index_root_docs(
        root_path: &Path,
        documents: &mut HashMap<String, DocumentContent>,
        keyword_index: &mut HashMap<String, Vec<String>>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let root_docs = vec![
            "README.md",
            "GLOBAL_THEORETICAL_FRAMEWORK_2025_10_20.md",
            "COMPREHENSIVE_ENHANCEMENT_FINAL_REPORT_2025_10_20.md",
            "MASTER_DOCUMENTATION_INDEX.md",
            "QUICK_START_GUIDE_2025_10_20.md",
            "PRACTICAL_PROJECTS_ROADMAP_2025_10_20.md",
            "DOCUMENTATION_TOOLCHAIN_DESIGN_2025_10_20.md",
            "FINAL_IMPLEMENTATION_SUMMARY_2025_10_20.md",
        ];

        for doc in root_docs {
            let file_path = root_path.join(doc);
            if file_path.exists() {
                Self::index_file(&file_path, "root", documents, keyword_index, &mut HashMap::new())?;
            }
        }

        Ok(())
    }

    /// 索引目录
    fn index_directory(
        dir_path: &Path,
        module_name: &str,
        documents: &mut HashMap<String, DocumentContent>,
        keyword_index: &mut HashMap<String, Vec<String>>,
        module_index: &mut HashMap<String, Vec<String>>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        for entry in fs::read_dir(dir_path)? {
            let entry = entry?;
            let path = entry.path();
            
            if path.is_file() && path.extension().and_then(|s| s.to_str()) == Some("md") {
                Self::index_file(&path, module_name, documents, keyword_index, module_index)?;
            }
        }
        Ok(())
    }

    /// 索引单个文件
    fn index_file(
        file_path: &Path,
        module_name: &str,
        documents: &mut HashMap<String, DocumentContent>,
        keyword_index: &mut HashMap<String, Vec<String>>,
        module_index: &mut HashMap<String, Vec<String>>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let content = fs::read_to_string(file_path)?;
        let lines: Vec<String> = content.lines().map(|s| s.to_string()).collect();
        
        let path_str = file_path.to_string_lossy().to_string();
        let doc_type = Self::detect_doc_type(&path_str);
        let keywords = Self::extract_keywords(&content);

        // 更新关键词索引
        for keyword in &keywords {
            keyword_index
                .entry(keyword.clone())
                .or_insert_with(Vec::new)
                .push(path_str.clone());
        }

        // 更新模块索引
        module_index
            .entry(module_name.to_string())
            .or_insert_with(Vec::new)
            .push(path_str.clone());

        // 存储文档内容
        documents.insert(
            path_str.clone(),
            DocumentContent {
                path: path_str,
                doc_type,
                module: module_name.to_string(),
                lines,
                keywords,
            },
        );

        Ok(())
    }

    /// 检测文档类型
    fn detect_doc_type(path: &str) -> DocumentType {
        if path.contains("KNOWLEDGE_GRAPH") {
            DocumentType::KnowledgeGraph
        } else if path.contains("MULTI_DIMENSIONAL") || path.contains("COMPARISON_MATRIX") {
            DocumentType::ComparisonMatrix
        } else if path.contains("MINDMAP") {
            DocumentType::MindMap
        } else if path.contains("EXAMPLES") {
            DocumentType::Examples
        } else if path.contains("REPORT") {
            DocumentType::Report
        } else if path.contains("THEORETICAL_FRAMEWORK") {
            DocumentType::Theory
        } else {
            DocumentType::MainDoc
        }
    }

    /// 提取关键词
    fn extract_keywords(content: &str) -> Vec<String> {
        let keywords = vec![
            // 核心概念
            "所有权", "ownership", "借用", "borrow", "生命周期", "lifetime",
            "类型系统", "type system", "泛型", "generic", "trait",
            "并发", "concurrency", "异步", "async", "多线程", "thread",
            
            // Rust 特性
            "Send", "Sync", "Arc", "Mutex", "RwLock", "Channel",
            "Future", "Pin", "Box", "Rc", "RefCell",
            
            // 设计模式
            "Builder", "Factory", "Singleton", "Observer", "Strategy",
            "Actor", "Reactor", "CSP",
            
            // 网络相关
            "TCP", "UDP", "HTTP", "WebSocket", "gRPC", "MQTT", "QUIC",
            "io_uring", "零拷贝", "zero-copy",
            
            // 理论
            "Hindley-Milner", "线性类型", "仿射类型", "范畴论",
            "分离逻辑", "形式化", "语义",
        ];

        keywords
            .into_iter()
            .filter(|&kw| content.contains(kw))
            .map(|s| s.to_string())
            .collect()
    }

    /// 执行搜索
    pub fn search(&self, query: &str, options: &SearchOptions) -> Vec<SearchResult> {
        // 根据搜索模式选择不同的搜索方法
        match &options.search_mode {
            SearchMode::Plain => self.search_plain(query, options),
            SearchMode::Regex => self.search_regex(query, options),
            SearchMode::Fuzzy => self.search_fuzzy(query, options),
        }
    }
    
    /// 普通搜索
    fn search_plain(&self, query: &str, options: &SearchOptions) -> Vec<SearchResult> {
        let mut results = Vec::new();
        let query_lower = query.to_lowercase();
        let query_terms: Vec<&str> = query_lower.split_whitespace().collect();

        for (path, doc_content) in &self.index.documents {
            // 过滤模块
            if let Some(module_filter) = &options.module_filter {
                if &doc_content.module != module_filter {
                    continue;
                }
            }

            // 过滤文档类型
            if let Some(type_filter) = &options.type_filter {
                if &doc_content.doc_type != type_filter {
                    continue;
                }
            }

            // 搜索匹配行
            for (line_num, line) in doc_content.lines.iter().enumerate() {
                let line_lower = line.to_lowercase();
                
                // 计算相关性分数
                let mut score = 0.0;
                let mut matches = 0;
                
                for term in &query_terms {
                    if line_lower.contains(term) {
                        matches += 1;
                        score += 1.0;
                        
                        // 标题匹配加分
                        if line.starts_with('#') {
                            score += 2.0;
                        }
                        
                        // 代码块匹配加分
                        if line.starts_with("```") {
                            score += 0.5;
                        }
                    }
                }

                // 关键词匹配加分
                for keyword in &doc_content.keywords {
                    if query_lower.contains(&keyword.to_lowercase()) {
                        score += 1.5;
                    }
                }

                if matches > 0 && score >= options.min_score {
                    // 获取上下文
                    let context = Self::get_context(&doc_content.lines, line_num, options.context_lines);
                    
                    results.push(SearchResult {
                        file_path: path.clone(),
                        line_number: line_num + 1,
                        context,
                        relevance_score: score,
                        doc_type: doc_content.doc_type.clone(),
                        module: doc_content.module.clone(),
                    });
                }
            }
        }

        // 排序和限制结果
        self.finalize_results(results, options)
    }
    
    /// 正则表达式搜索
    fn search_regex(&self, pattern: &str, options: &SearchOptions) -> Vec<SearchResult> {
        let regex_searcher = match RegexSearcher::new(pattern) {
            Ok(s) => s,
            Err(_) => return Vec::new(),
        };
        
        let mut results = Vec::new();
        
        for (path, doc_content) in &self.index.documents {
            if !self.should_include_document(doc_content, options) {
                continue;
            }
            
            let matches = regex_searcher.find_in_lines(&doc_content.lines);
            
            for (line_num, line_matches) in matches {
                let score = line_matches.len() as f64 * 2.0; // 正则匹配给予更高分数
                
                if score >= options.min_score {
                    let context = Self::get_context(&doc_content.lines, line_num, options.context_lines);
                    
                    results.push(SearchResult {
                        file_path: path.clone(),
                        line_number: line_num + 1,
                        context,
                        relevance_score: score,
                        doc_type: doc_content.doc_type.clone(),
                        module: doc_content.module.clone(),
                    });
                }
            }
        }
        
        self.finalize_results(results, options)
    }
    
    /// 模糊搜索
    fn search_fuzzy(&self, query: &str, options: &SearchOptions) -> Vec<SearchResult> {
        let fuzzy_searcher = FuzzySearcher::new(self.config.advanced.fuzzy_threshold);
        let mut results = Vec::new();
        
        for (path, doc_content) in &self.index.documents {
            if !self.should_include_document(doc_content, options) {
                continue;
            }
            
            let matches = fuzzy_searcher.fuzzy_match_lines(query, &doc_content.lines);
            
            for (line_num, score) in matches {
                if score >= options.min_score {
                    let context = Self::get_context(&doc_content.lines, line_num, options.context_lines);
                    
                    results.push(SearchResult {
                        file_path: path.clone(),
                        line_number: line_num + 1,
                        context,
                        relevance_score: score * 10.0, // 归一化分数
                        doc_type: doc_content.doc_type.clone(),
                        module: doc_content.module.clone(),
                    });
                }
            }
        }
        
        self.finalize_results(results, options)
    }
    
    /// 检查是否应该包含该文档
    fn should_include_document(&self, doc_content: &DocumentContent, options: &SearchOptions) -> bool {
        // 过滤模块
        if let Some(module_filter) = &options.module_filter {
            if &doc_content.module != module_filter {
                return false;
            }
        }
        
        // 过滤文档类型
        if let Some(type_filter) = &options.type_filter {
            if &doc_content.doc_type != type_filter {
                return false;
            }
        }
        
        true
    }
    
    /// 完成结果处理（排序和限制）
    fn finalize_results(&self, mut results: Vec<SearchResult>, options: &SearchOptions) -> Vec<SearchResult> {
        // 排序结果
        results.sort_by(|a, b| {
            b.relevance_score
                .partial_cmp(&a.relevance_score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        // 限制结果数量
        results.truncate(options.max_results);
        results
    }

    /// 获取上下文
    fn get_context(lines: &[String], line_num: usize, context_lines: usize) -> String {
        let start = line_num.saturating_sub(context_lines);
        let end = (line_num + context_lines + 1).min(lines.len());
        
        lines[start..end].join("\n")
    }

    /// 按模块搜索
    pub fn search_by_module(&self, module: &str) -> Vec<String> {
        self.index
            .module_index
            .get(module)
            .cloned()
            .unwrap_or_default()
    }

    /// 按关键词搜索
    pub fn search_by_keyword(&self, keyword: &str) -> Vec<String> {
        self.index
            .keyword_index
            .get(keyword)
            .cloned()
            .unwrap_or_default()
    }

    /// 获取所有模块
    pub fn get_modules(&self) -> Vec<String> {
        self.index.module_index.keys().cloned().collect()
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> SearchStats {
        SearchStats {
            total_documents: self.index.documents.len(),
            total_modules: self.index.module_index.len(),
            total_keywords: self.index.keyword_index.len(),
            documents_by_type: self.count_by_type(),
        }
    }

    /// 按类型统计文档
    fn count_by_type(&self) -> HashMap<DocumentType, usize> {
        let mut counts = HashMap::new();
        for doc in self.index.documents.values() {
            *counts.entry(doc.doc_type.clone()).or_insert(0) += 1;
        }
        counts
    }
}

/// 搜索模式
#[derive(Debug, Clone)]
pub enum SearchMode {
    /// 普通搜索
    Plain,
    /// 正则表达式搜索
    Regex,
    /// 模糊搜索
    Fuzzy,
}

/// 搜索选项
#[derive(Debug, Clone)]
pub struct SearchOptions {
    /// 模块过滤
    pub module_filter: Option<String>,
    /// 文档类型过滤
    pub type_filter: Option<DocumentType>,
    /// 最小相关性分数
    pub min_score: f64,
    /// 最大结果数量
    pub max_results: usize,
    /// 搜索模式
    pub search_mode: SearchMode,
    /// 上下文行数
    pub context_lines: usize,
}

impl Default for SearchOptions {
    fn default() -> Self {
        Self {
            module_filter: None,
            type_filter: None,
            min_score: 1.0,
            max_results: 50,
            search_mode: SearchMode::Plain,
            context_lines: 2,
        }
    }
}

/// 搜索统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchStats {
    pub total_documents: usize,
    pub total_modules: usize,
    pub total_keywords: usize,
    pub documents_by_type: HashMap<DocumentType, usize>,
}

mod cli;
mod config;
mod export;
mod cache;
mod fuzzy;

pub use config::{Config, ExportFormat};
pub use export::export_results;
pub use cache::{IndexCache, CacheMetadata};
pub use fuzzy::{FuzzySearcher, RegexSearcher, SearchPattern};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    cli::run()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_doc_type_detection() {
        assert_eq!(
            DocSearcher::detect_doc_type("docs/theory/KNOWLEDGE_GRAPH_AND_CONCEPT_RELATIONS.md"),
            DocumentType::KnowledgeGraph
        );
        assert_eq!(
            DocSearcher::detect_doc_type("docs/MULTI_DIMENSIONAL_COMPARISON_MATRIX.md"),
            DocumentType::ComparisonMatrix
        );
    }

    #[test]
    fn test_keyword_extraction() {
        let content = "Rust 所有权系统是一个基于借用检查的内存安全机制";
        let keywords = DocSearcher::extract_keywords(content);
        assert!(keywords.contains(&"所有权".to_string()));
        assert!(keywords.contains(&"借用".to_string()));
    }
}

