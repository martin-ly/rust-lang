// CLI 命令行界面实现

use clap::{Parser, Subcommand};
use colored::*;
use std::path::PathBuf;

use crate::{DocSearcher, DocumentType, SearchOptions, SearchMode, Config, export_results};

/// Rust 学习项目 - 智能文档搜索工具
#[derive(Parser)]
#[command(name = "rust-doc-search")]
#[command(about = "🔍 智能搜索 Rust 学习项目文档", long_about = None)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Subcommand)]
pub enum Commands {
    /// 搜索文档
    Search {
        /// 搜索关键词
        query: String,
        
        /// 过滤模块
        #[arg(short, long)]
        module: Option<String>,
        
        /// 过滤文档类型
        #[arg(short, long)]
        doc_type: Option<String>,
        
        /// 最大结果数
        #[arg(short = 'n', long, default_value = "20")]
        max_results: usize,
        
        /// 最小分数
        #[arg(short = 's', long, default_value = "1.0")]
        min_score: f64,
        
        /// 使用正则表达式搜索
        #[arg(short = 'r', long)]
        regex: bool,
        
        /// 使用模糊搜索
        #[arg(short = 'f', long)]
        fuzzy: bool,
        
        /// 导出结果到文件
        #[arg(short = 'o', long)]
        output: Option<PathBuf>,
        
        /// 导出格式 (json, csv, markdown)
        #[arg(short = 'F', long, default_value = "json")]
        format: String,
        
        /// 上下文行数
        #[arg(short = 'c', long, default_value = "2")]
        context_lines: usize,
    },
    
    /// 显示统计信息
    Stats,
    
    /// 列出所有模块
    Modules,
    
    /// 按模块搜索
    Module {
        /// 模块名称
        name: String,
    },
    
    /// 按关键词搜索
    Keyword {
        /// 关键词
        keyword: String,
    },
    
    /// 生成配置文件模板
    InitConfig {
        /// 配置文件路径
        #[arg(short, long)]
        path: Option<PathBuf>,
    },
    
    /// 清除缓存
    ClearCache,
}

pub fn run() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    
    println!("{}", "🔍 Rust 学习项目 - 智能文档搜索工具 v1.1".bright_cyan().bold());
    println!();

    // 获取项目根目录（向上两级）
    let mut root_path = std::env::current_dir()?;
    root_path.pop(); // 从 tools/doc_search 到 tools
    root_path.pop(); // 从 tools 到项目根
    
    // 处理不需要索引的命令
    match &cli.command {
        Commands::InitConfig { path } => {
            return init_config(path.as_deref());
        }
        Commands::ClearCache => {
            return clear_cache();
        }
        _ => {}
    }
    
    print!("{}", "📂 正在构建文档索引... ".yellow());
    let searcher = DocSearcher::new(&root_path)?;
    println!("{}", "✅".green());
    println!();

    match cli.command {
        Commands::Search {
            query,
            module,
            doc_type,
            max_results,
            min_score,
            regex,
            fuzzy,
            output,
            format,
            context_lines,
        } => {
            let type_filter = doc_type.as_ref().and_then(|t| parse_doc_type(t));
            
            // 确定搜索模式
            let search_mode = if regex {
                SearchMode::Regex
            } else if fuzzy {
                SearchMode::Fuzzy
            } else {
                SearchMode::Plain
            };
            
            let options = SearchOptions {
                module_filter: module.clone(),
                type_filter,
                min_score,
                max_results,
                search_mode,
                context_lines,
            };
            
            println!("{} '{}'", "🔍 搜索:".bright_blue().bold(), query.bright_white().bold());
            if regex {
                println!("   {} {}", "搜索模式:".bright_blue(), "正则表达式".bright_yellow());
            } else if fuzzy {
                println!("   {} {}", "搜索模式:".bright_blue(), "模糊搜索".bright_yellow());
            }
            if let Some(m) = &module {
                println!("   {} {}", "模块过滤:".bright_blue(), m.bright_white());
            }
            if let Some(t) = &doc_type {
                println!("   {} {}", "类型过滤:".bright_blue(), t.bright_white());
            }
            println!();
            
            let results = searcher.search(&query, &options);
            
            if results.is_empty() {
                println!("{}", "❌ 未找到匹配结果".red());
                return Ok(());
            }
            
            println!("{} {} 个结果", "✅ 找到".green(), results.len().to_string().bright_white().bold());
            println!("{}", "─".repeat(80).bright_black());
            println!();
            
            // 导出结果
            if let Some(output_path) = output {
                let export_format = parse_export_format(&format);
                export_results(&results, &output_path, &export_format)?;
                println!("{} {}", "💾 结果已导出到:".green(), output_path.display().to_string().bright_cyan());
                println!();
            }
            
            for (i, result) in results.iter().enumerate() {
                let rank = format!("{}.", i + 1);
                println!("{} {} {}:{}",
                         rank.bright_yellow().bold(),
                         get_doc_type_icon(&result.doc_type),
                         result.file_path.bright_cyan(),
                         result.line_number.to_string().bright_magenta());
                
                println!("   {} {} | {} {:?} | {} {:.1}",
                         "模块:".bright_black(),
                         result.module.bright_white(),
                         "类型:".bright_black(),
                         result.doc_type,
                         "分数:".bright_black(),
                         result.relevance_score);
                
                // 显示匹配内容（高亮关键词）
                let preview = result.context.lines().take(2).collect::<Vec<_>>().join(" ");
                let preview = if preview.len() > 100 {
                    format!("{}...", &preview[..100])
                } else {
                    preview
                };
                println!("   {}", preview.bright_black());
                println!();
            }
        }
        
        Commands::Stats => {
            let stats = searcher.get_stats();
            
            println!("{}", "📊 文档统计信息".bright_cyan().bold());
            println!("{}", "─".repeat(80).bright_black());
            println!();
            
            println!("{} {}", "📄 总文档数:".bright_blue(), stats.total_documents.to_string().bright_white().bold());
            println!("{} {}", "📦 总模块数:".bright_blue(), stats.total_modules.to_string().bright_white().bold());
            println!("{} {}", "🔑 总关键词数:".bright_blue(), stats.total_keywords.to_string().bright_white().bold());
            println!();
            
            println!("{}", "📚 文档类型分布:".bright_cyan().bold());
            for (doc_type, count) in &stats.documents_by_type {
                println!("   {} {:?}: {}",
                         get_doc_type_icon(doc_type),
                         doc_type,
                         count.to_string().bright_white());
            }
        }
        
        Commands::Modules => {
            let modules = searcher.get_modules();
            
            println!("{}", "📦 所有模块".bright_cyan().bold());
            println!("{}", "─".repeat(80).bright_black());
            println!();
            
            for (i, module) in modules.iter().enumerate() {
                println!("{} {}", 
                         format!("{}.", i + 1).bright_yellow(),
                         module.bright_white());
            }
        }
        
        Commands::Module { name } => {
            let docs = searcher.search_by_module(&name);
            
            println!("{} '{}'", "📦 模块文档:".bright_cyan().bold(), name.bright_white().bold());
            println!("{}", "─".repeat(80).bright_black());
            println!();
            
            if docs.is_empty() {
                println!("{}", "❌ 未找到该模块".red());
                return Ok(());
            }
            
            for (i, doc) in docs.iter().enumerate() {
                println!("{} {}", 
                         format!("{}.", i + 1).bright_yellow(),
                         doc.bright_cyan());
            }
        }
        
        Commands::Keyword { keyword } => {
            let docs = searcher.search_by_keyword(&keyword);
            
            println!("{} '{}'", "🔑 关键词文档:".bright_cyan().bold(), keyword.bright_white().bold());
            println!("{}", "─".repeat(80).bright_black());
            println!();
            
            if docs.is_empty() {
                println!("{}", "❌ 未找到包含该关键词的文档".red());
                return Ok(());
            }
            
            for (i, doc) in docs.iter().enumerate() {
                println!("{} {}", 
                         format!("{}.", i + 1).bright_yellow(),
                         doc.bright_cyan());
            }
        }
        
        Commands::InitConfig { .. } | Commands::ClearCache => {
            // 已在前面处理
            unreachable!()
        }
    }
    
    Ok(())
}

/// 初始化配置文件
fn init_config(path: Option<&std::path::Path>) -> Result<(), Box<dyn std::error::Error>> {
    let config = Config::default();
    
    let config_path = if let Some(p) = path {
        p.to_path_buf()
    } else {
        Config::default_config_path()
            .ok_or("无法确定默认配置路径")?
    };
    
    config.save_to_file(&config_path)?;
    
    println!("{} {}", "✅ 配置文件已创建:".green(), config_path.display().to_string().bright_cyan());
    println!();
    println!("{}", "配置文件内容:".bright_blue().bold());
    println!("{}", "─".repeat(80).bright_black());
    
    let content = std::fs::read_to_string(&config_path)?;
    println!("{}", content);
    
    Ok(())
}

/// 清除缓存
fn clear_cache() -> Result<(), Box<dyn std::error::Error>> {
    use crate::IndexCache;
    
    if let Some(cache_path) = IndexCache::default_cache_path() {
        if cache_path.exists() {
            std::fs::remove_file(&cache_path)?;
            println!("{} {}", "✅ 缓存已清除:".green(), cache_path.display().to_string().bright_cyan());
        } else {
            println!("{}", "ℹ️  缓存不存在".yellow());
        }
    } else {
        println!("{}", "❌ 无法确定缓存路径".red());
    }
    
    Ok(())
}

/// 解析导出格式
fn parse_export_format(s: &str) -> crate::ExportFormat {
    match s.to_lowercase().as_str() {
        "json" => crate::ExportFormat::Json,
        "csv" => crate::ExportFormat::Csv,
        "markdown" | "md" => crate::ExportFormat::Markdown,
        _ => crate::ExportFormat::Json,
    }
}

fn parse_doc_type(s: &str) -> Option<DocumentType> {
    match s.to_lowercase().as_str() {
        "knowledge" | "graph" => Some(DocumentType::KnowledgeGraph),
        "matrix" | "comparison" => Some(DocumentType::ComparisonMatrix),
        "mindmap" | "mind" => Some(DocumentType::MindMap),
        "examples" | "example" => Some(DocumentType::Examples),
        "report" => Some(DocumentType::Report),
        "main" | "readme" => Some(DocumentType::MainDoc),
        "theory" => Some(DocumentType::Theory),
        _ => None,
    }
}

fn get_doc_type_icon(doc_type: &DocumentType) -> &'static str {
    match doc_type {
        DocumentType::KnowledgeGraph => "📊",
        DocumentType::ComparisonMatrix => "📐",
        DocumentType::MindMap => "🗺️",
        DocumentType::Examples => "💻",
        DocumentType::Report => "📋",
        DocumentType::MainDoc => "📘",
        DocumentType::Theory => "🎓",
    }
}

