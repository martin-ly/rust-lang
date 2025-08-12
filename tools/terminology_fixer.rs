use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::io::{self, Write};

#[derive(Debug)]
pub struct TermReplacement {
    pub incorrect: String,
    pub correct: String,
    pub context: String,
}

#[derive(Debug)]
pub struct FixResult {
    pub file_path: String,
    pub replacements_made: usize,
    pub total_terms: usize,
    pub success: bool,
    pub error_message: Option<String>,
}

pub struct TerminologyFixer {
    pub replacement_mappings: HashMap<String, String>,
    pub backup_enabled: bool,
    pub dry_run: bool,
}

impl TerminologyFixer {
    pub fn new() -> Self {
        let mut replacement_mappings = HashMap::new();
        
        // 核心术语修正映射
        replacement_mappings.insert("特性".to_string(), "特征".to_string());
        replacement_mappings.insert("拥有权".to_string(), "所有权".to_string());
        replacement_mappings.insert("生存期".to_string(), "生命周期".to_string());
        replacement_mappings.insert("转移".to_string(), "移动".to_string());
        replacement_mappings.insert("拷贝".to_string(), "复制".to_string());
        replacement_mappings.insert("结构".to_string(), "结构体".to_string());
        replacement_mappings.insert("联合".to_string(), "联合体".to_string());
        replacement_mappings.insert("内存安全性".to_string(), "内存安全".to_string());
        replacement_mappings.insert("并发性".to_string(), "并发".to_string());
        replacement_mappings.insert("并行性".to_string(), "并行".to_string());
        replacement_mappings.insert("互斥量".to_string(), "互斥锁".to_string());
        replacement_mappings.insert("未来".to_string(), "未来值".to_string());
        replacement_mappings.insert("堆栈".to_string(), "栈".to_string());
        replacement_mappings.insert("堆内存".to_string(), "堆".to_string());
        replacement_mappings.insert("范围".to_string(), "作用域".to_string());
        replacement_mappings.insert("安全性".to_string(), "安全".to_string());
        replacement_mappings.insert("验证".to_string(), "验证".to_string());
        replacement_mappings.insert("性能".to_string(), "性能".to_string());
        replacement_mappings.insert("优化".to_string(), "优化".to_string());
        
        Self {
            replacement_mappings,
            backup_enabled: true,
            dry_run: false,
        }
    }
    
    pub fn fix_document(&self, document_path: &Path) -> Result<FixResult, io::Error> {
        let content = fs::read_to_string(document_path)?;
        let original_content = content.clone();
        
        let mut fixed_content = content;
        let mut replacements_made = 0;
        let mut total_terms = 0;
        
        // 统计原始术语数量
        for (incorrect, _) in &self.replacement_mappings {
            total_terms += fixed_content.matches(incorrect).count();
        }
        
        // 执行术语替换
        for (incorrect, correct) in &self.replacement_mappings {
            let count = fixed_content.matches(incorrect).count();
            if count > 0 {
                fixed_content = fixed_content.replace(incorrect, correct);
                replacements_made += count;
            }
        }
        
        // 如果不是试运行，则写入文件
        if !self.dry_run {
            // 创建备份
            if self.backup_enabled {
                let backup_path = document_path.with_extension("md.backup");
                fs::write(&backup_path, &original_content)?;
            }
            
            // 写入修正后的内容
            fs::write(document_path, &fixed_content)?;
        }
        
        Ok(FixResult {
            file_path: document_path.to_string_lossy().to_string(),
            replacements_made,
            total_terms,
            success: true,
            error_message: None,
        })
    }
    
    pub fn fix_directory(&self, dir_path: &Path) -> Result<Vec<FixResult>, io::Error> {
        let mut results = Vec::new();
        
        if dir_path.is_dir() {
            for entry in fs::read_dir(dir_path)? {
                let entry = entry?;
                let path = entry.path();
                
                if path.is_file() && path.extension().map_or(false, |ext| ext == "md") {
                    match self.fix_document(&path) {
                        Ok(result) => results.push(result),
                        Err(e) => {
                            results.push(FixResult {
                                file_path: path.to_string_lossy().to_string(),
                                replacements_made: 0,
                                total_terms: 0,
                                success: false,
                                error_message: Some(e.to_string()),
                            });
                        }
                    }
                } else if path.is_dir() {
                    let sub_results = self.fix_directory(&path)?;
                    results.extend(sub_results);
                }
            }
        }
        
        Ok(results)
    }
    
    pub fn generate_report(&self, results: &[FixResult]) -> String {
        let mut report = String::new();
        
        report.push_str("# 术语批量修正报告\n\n");
        
        // 总体统计
        let total_files = results.len();
        let successful_files = results.iter().filter(|r| r.success).count();
        let total_replacements: usize = results.iter().map(|r| r.replacements_made).sum();
        let total_terms: usize = results.iter().map(|r| r.total_terms).sum();
        
        report.push_str(&format!("## 总体统计\n"));
        report.push_str(&format!("- **处理文件数**: {}\n", total_files));
        report.push_str(&format!("- **成功文件数**: {}\n", successful_files));
        report.push_str(&format!("- **失败文件数**: {}\n", total_files - successful_files));
        report.push_str(&format!("- **总修正数**: {}\n", total_replacements));
        report.push_str(&format!("- **总术语数**: {}\n", total_terms));
        report.push_str(&format!("- **修正率**: {:.2}%\n\n", 
            if total_terms > 0 { total_replacements as f64 / total_terms as f64 * 100.0 } else { 0.0 }));
        
        // 成功文件详情
        if successful_files > 0 {
            report.push_str("## 成功修正文件\n\n");
            for result in results.iter().filter(|r| r.success && r.replacements_made > 0) {
                report.push_str(&format!("### {}\n", result.file_path));
                report.push_str(&format!("- **修正数**: {}\n", result.replacements_made));
                report.push_str(&format!("- **总术语数**: {}\n", result.total_terms));
                report.push_str(&format!("- **修正率**: {:.2}%\n\n", 
                    if result.total_terms > 0 { result.replacements_made as f64 / result.total_terms as f64 * 100.0 } else { 0.0 }));
            }
        }
        
        // 失败文件详情
        let failed_files: Vec<_> = results.iter().filter(|r| !r.success).collect();
        if !failed_files.is_empty() {
            report.push_str("## 失败文件\n\n");
            for result in failed_files {
                report.push_str(&format!("### {}\n", result.file_path));
                report.push_str(&format!("- **错误**: {}\n\n", 
                    result.error_message.as_ref().unwrap_or(&"未知错误".to_string())));
            }
        }
        
        // 修正映射详情
        report.push_str("## 修正映射详情\n\n");
        for (incorrect, correct) in &self.replacement_mappings {
            report.push_str(&format!("- **{}** → **{}**\n", incorrect, correct));
        }
        
        report
    }
    
    pub fn set_dry_run(&mut self, dry_run: bool) {
        self.dry_run = dry_run;
    }
    
    pub fn set_backup_enabled(&mut self, backup_enabled: bool) {
        self.backup_enabled = backup_enabled;
    }
}

fn main() -> Result<(), io::Error> {
    let args: Vec<String> = std::env::args().collect();
    
    if args.len() < 2 {
        println!("用法: terminology_fixer <目录路径> [--dry-run] [--no-backup]");
        return Ok(());
    }
    
    let dir_path = PathBuf::from(&args[1]);
    let dry_run = args.contains(&"--dry-run".to_string());
    let no_backup = args.contains(&"--no-backup".to_string());
    
    if !dir_path.exists() {
        eprintln!("错误: 目录不存在: {}", dir_path.display());
        return Ok(());
    }
    
    let mut fixer = TerminologyFixer::new();
    fixer.set_dry_run(dry_run);
    fixer.set_backup_enabled(!no_backup);
    
    println!("开始术语批量修正...");
    println!("目录: {}", dir_path.display());
    println!("试运行: {}", dry_run);
    println!("备份: {}", !no_backup);
    println!();
    
    let results = fixer.fix_directory(&dir_path)?;
    
    // 生成报告
    let report = fixer.generate_report(&results);
    
    // 保存报告
    let report_path = dir_path.join("terminology_fix_report.md");
    fs::write(&report_path, &report)?;
    
    // 输出摘要
    let total_files = results.len();
    let successful_files = results.iter().filter(|r| r.success).count();
    let total_replacements: usize = results.iter().map(|r| r.replacements_made).sum();
    
    println!("修正完成!");
    println!("处理文件: {}", total_files);
    println!("成功文件: {}", successful_files);
    println!("总修正数: {}", total_replacements);
    println!("报告已保存: {}", report_path.display());
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::tempdir;
    
    #[test]
    fn test_terminology_fixer() {
        let temp_dir = tempdir().unwrap();
        let test_file = temp_dir.path().join("test.md");
        
        // 创建测试文件
        let test_content = r#"
# 测试文档

这是一个测试文档，包含一些需要修正的术语。

## 特性分析
Rust的trait特性非常强大。

## 所有权系统
变量的拥有权管理是Rust的核心。

## 并发编程
Rust的并发性模型很优秀。
"#;
        
        fs::write(&test_file, test_content).unwrap();
        
        // 创建修正器
        let mut fixer = TerminologyFixer::new();
        fixer.set_dry_run(true); // 试运行
        
        // 执行修正
        let result = fixer.fix_document(&test_file).unwrap();
        
        // 验证结果
        assert!(result.success);
        assert_eq!(result.replacements_made, 3); // 特性、拥有权、并发性
        assert_eq!(result.total_terms, 3);
        
        // 验证文件内容未改变（因为是试运行）
        let content_after = fs::read_to_string(&test_file).unwrap();
        assert_eq!(content_after, test_content);
    }
} 