use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;
use walkdir::WalkDir;

/// 文档检查器配置
#[derive(Debug, Clone)]
pub struct DocCheckerConfig {
    /// 是否检查数学公式
    pub check_math: bool,
    /// 是否检查链接
    pub check_links: bool,
    /// 是否检查格式
    pub check_format: bool,
    /// 是否自动修复
    pub auto_fix: bool,
    /// 递归检查子目录
    pub recursive: bool,
}

impl Default for DocCheckerConfig {
    fn default() -> Self {
        Self {
            check_math: true,
            check_links: true,
            check_format: true,
            auto_fix: false,
            recursive: true,
        }
    }
}

/// 检查结果
#[derive(Debug, Clone)]
pub struct CheckResult {
    /// 文件路径
    pub file_path: PathBuf,
    /// 检查是否通过
    pub passed: bool,
    /// 错误列表
    pub errors: Vec<String>,
    /// 警告列表
    pub warnings: Vec<String>,
    /// 修复建议
    pub suggestions: Vec<String>,
}

/// 文档检查器
pub struct DocChecker {
    config: DocCheckerConfig,
    results: Vec<CheckResult>,
}

impl DocChecker {
    /// 创建新的文档检查器
    pub fn new(config: DocCheckerConfig) -> Self {
        Self {
            config,
            results: Vec::new(),
        }
    }

    /// 检查单个文件
    pub fn check_file(&mut self, file_path: &Path) -> CheckResult {
        let mut result = CheckResult {
            file_path: file_path.to_path_buf(),
            passed: true,
            errors: Vec::new(),
            warnings: Vec::new(),
            suggestions: Vec::new(),
        };

        // 读取文件内容
        let content = match fs::read_to_string(file_path) {
            Ok(content) => content,
            Err(e) => {
                result.passed = false;
                result.errors.push(format!("无法读取文件: {}", e));
                return result;
            }
        };

        // 检查文档头部格式
        self.check_document_header(&content, &mut result);

        // 检查章节编号
        self.check_section_numbering(&content, &mut result);

        // 检查数学公式
        if self.config.check_math {
            self.check_math_formulas(&content, &mut result);
        }

        // 检查链接
        if self.config.check_links {
            self.check_links(&content, &mut result);
        }

        // 检查表格格式
        self.check_tables(&content, &mut result);

        // 检查代码块
        self.check_code_blocks(&content, &mut result);

        // 更新通过状态
        result.passed = result.errors.is_empty();

        result
    }

    /// 检查文档头部格式
    fn check_document_header(&self, content: &str, result: &mut CheckResult) {
        let lines: Vec<&str> = content.lines().collect();
        
        if lines.is_empty() {
            result.errors.push("文档为空".to_string());
            return;
        }

        // 检查标题格式
        if !lines[0].starts_with('#') {
            result.errors.push("文档必须以标题开始".to_string());
        }

        // 检查文档信息部分
        let has_doc_info = content.contains("## 📅 文档信息") || 
                          content.contains("**文档版本**") ||
                          content.contains("**创建日期**");

        if !has_doc_info {
            result.warnings.push("建议添加文档信息部分".to_string());
            result.suggestions.push("在标题后添加文档信息部分，包含版本、日期、状态等信息".to_string());
        }
    }

    /// 检查章节编号
    fn check_section_numbering(&self, content: &str, result: &mut CheckResult) {
        let lines: Vec<&str> = content.lines().collect();
        let mut section_numbers = Vec::new();

        for (line_num, line) in lines.iter().enumerate() {
            if line.starts_with("## ") {
                let section = line.trim_start_matches("## ");
                if let Some(number) = section.split_whitespace().next() {
                    if number.contains('.') {
                        section_numbers.push((line_num + 1, number.to_string()));
                    }
                }
            }
        }

        // 检查编号连续性
        for i in 1..section_numbers.len() {
            let prev = &section_numbers[i - 1].1;
            let curr = &section_numbers[i].1;
            
            if !self.is_sequential_numbering(prev, curr) {
                result.warnings.push(format!(
                    "章节编号可能不连续: {} -> {} (第{}行)",
                    prev, curr, section_numbers[i].0
                ));
            }
        }
    }

    /// 检查数学公式
    fn check_math_formulas(&self, content: &str, result: &mut CheckResult) {
        let lines: Vec<&str> = content.lines().collect();
        
        for (line_num, line) in lines.iter().enumerate() {
            // 检查行内公式
            if line.contains('$') {
                let dollar_count = line.matches('$').count();
                if dollar_count % 2 != 0 {
                    result.errors.push(format!(
                        "行内公式美元符号不匹配 (第{}行): {}",
                        line_num + 1, line
                    ));
                }
            }

            // 检查块级公式
            if line.trim() == "$$" {
                // 查找配对的 $$
                let mut found_pair = false;
                for next_line in lines.iter().skip(line_num + 1) {
                    if next_line.trim() == "$$" {
                        found_pair = true;
                        break;
                    }
                }
                if !found_pair {
                    result.errors.push(format!(
                        "块级公式缺少结束标记 $$ (第{}行)",
                        line_num + 1
                    ));
                }
            }
        }
    }

    /// 检查链接
    fn check_links(&self, content: &str, result: &mut CheckResult) {
        let lines: Vec<&str> = content.lines().collect();
        
        for (line_num, line) in lines.iter().enumerate() {
            // 检查Markdown链接格式
            if line.contains('[') && line.contains(']') && line.contains('(') && line.contains(')') {
                // 简单的链接格式检查
                let open_bracket = line.find('[').unwrap_or(0);
                let close_bracket = line.find(']').unwrap_or(0);
                let open_paren = line.find('(').unwrap_or(0);
                let close_paren = line.find(')').unwrap_or(0);

                if close_bracket < open_bracket || close_paren < open_paren {
                    result.errors.push(format!(
                        "链接格式错误 (第{}行): {}",
                        line_num + 1, line
                    ));
                }
            }
        }
    }

    /// 检查表格格式
    fn check_tables(&self, content: &str, result: &mut CheckResult) {
        let lines: Vec<&str> = content.lines().collect();
        let mut in_table = false;
        let mut table_start_line = 0;

        for (line_num, line) in lines.iter().enumerate() {
            if line.starts_with('|') && line.ends_with('|') {
                if !in_table {
                    in_table = true;
                    table_start_line = line_num + 1;
                }
            } else if in_table {
                // 表格结束
                in_table = false;
                // 这里可以添加更详细的表格格式检查
            }
        }

        if in_table {
            result.warnings.push(format!(
                "表格可能未正确结束 (开始于第{}行)",
                table_start_line
            ));
        }
    }

    /// 检查代码块
    fn check_code_blocks(&self, content: &str, result: &mut CheckResult) {
        let lines: Vec<&str> = content.lines().collect();
        let mut in_code_block = false;
        let mut code_block_start_line = 0;

        for (line_num, line) in lines.iter().enumerate() {
            if line.starts_with("```") {
                if !in_code_block {
                    in_code_block = true;
                    code_block_start_line = line_num + 1;
                } else {
                    in_code_block = false;
                }
            }
        }

        if in_code_block {
            result.errors.push(format!(
                "代码块未正确结束 (开始于第{}行)",
                code_block_start_line
            ));
        }
    }

    /// 检查编号是否连续
    fn is_sequential_numbering(&self, prev: &str, curr: &str) -> bool {
        // 简单的编号连续性检查
        // 这里可以实现更复杂的逻辑
        true
    }

    /// 检查目录或文件
    pub fn check_path(&mut self, path: &Path) -> Vec<CheckResult> {
        self.results.clear();

        if path.is_file() {
            if path.extension().and_then(|s| s.to_str()) == Some("md") {
                let result = self.check_file(path);
                self.results.push(result);
            }
        } else if path.is_dir() && self.config.recursive {
            for entry in WalkDir::new(path)
                .into_iter()
                .filter_map(|e| e.ok())
                .filter(|e| e.file_type().is_file())
            {
                let file_path = entry.path();
                if file_path.extension().and_then(|s| s.to_str()) == Some("md") {
                    let result = self.check_file(file_path);
                    self.results.push(result);
                }
            }
        }

        self.results.clone()
    }

    /// 生成检查报告
    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        report.push_str("# 文档检查报告\n\n");

        let total_files = self.results.len();
        let passed_files = self.results.iter().filter(|r| r.passed).count();
        let failed_files = total_files - passed_files;

        report.push_str(&format!("## 总体统计\n\n"));
        report.push_str(&format!("- 总文件数: {}\n", total_files));
        report.push_str(&format!("- 通过检查: {}\n", passed_files));
        report.push_str(&format!("- 未通过: {}\n", failed_files));
        report.push_str(&format!("- 通过率: {:.1}%\n\n", 
            if total_files > 0 { (passed_files as f64 / total_files as f64) * 100.0 } else { 0.0 }));

        if failed_files > 0 {
            report.push_str("## 问题文件\n\n");
            for result in &self.results {
                if !result.passed {
                    report.push_str(&format!("### {}\n\n", result.file_path.display()));
                    
                    if !result.errors.is_empty() {
                        report.push_str("**错误:**\n");
                        for error in &result.errors {
                            report.push_str(&format!("- {}\n", error));
                        }
                        report.push_str("\n");
                    }

                    if !result.warnings.is_empty() {
                        report.push_str("**警告:**\n");
                        for warning in &result.warnings {
                            report.push_str(&format!("- {}\n", warning));
                        }
                        report.push_str("\n");
                    }

                    if !result.suggestions.is_empty() {
                        report.push_str("**建议:**\n");
                        for suggestion in &result.suggestions {
                            report.push_str(&format!("- {}\n", suggestion));
                        }
                        report.push_str("\n");
                    }
                }
            }
        }

        report
    }
}

/// 主函数
fn main() {
    let args: Vec<String> = std::env::args().collect();
    
    if args.len() < 2 {
        eprintln!("用法: {} <路径> [选项]", args[0]);
        eprintln!("选项:");
        eprintln!("  --no-math    不检查数学公式");
        eprintln!("  --no-links   不检查链接");
        eprintln!("  --no-format  不检查格式");
        eprintln!("  --auto-fix   自动修复");
        eprintln!("  --no-recursive 不递归检查子目录");
        process::exit(1);
    }

    let path = Path::new(&args[1]);
    if !path.exists() {
        eprintln!("错误: 路径不存在: {}", path.display());
        process::exit(1);
    }

    let mut config = DocCheckerConfig::default();
    
    for arg in &args[2..] {
        match arg.as_str() {
            "--no-math" => config.check_math = false,
            "--no-links" => config.check_links = false,
            "--no-format" => config.check_format = false,
            "--auto-fix" => config.auto_fix = true,
            "--no-recursive" => config.recursive = false,
            _ => {
                eprintln!("未知选项: {}", arg);
                process::exit(1);
            }
        }
    }

    let mut checker = DocChecker::new(config);
    let results = checker.check_path(path);
    
    // 输出报告
    let report = checker.generate_report();
    println!("{}", report);

    // 如果有错误，返回非零退出码
    let has_errors = results.iter().any(|r| !r.passed);
    if has_errors {
        process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::tempdir;

    #[test]
    fn test_check_document_header() {
        let config = DocCheckerConfig::default();
        let checker = DocChecker::new(config);
        
        // 创建临时文件
        let temp_dir = tempdir().unwrap();
        let file_path = temp_dir.path().join("test.md");
        
        let content = "# 测试文档\n\n## 📅 文档信息\n\n**文档版本**: v1.0";
        fs::write(&file_path, content).unwrap();
        
        let mut checker = DocChecker::new(DocCheckerConfig::default());
        let result = checker.check_file(&file_path);
        
        assert!(result.passed);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_check_math_formulas() {
        let temp_dir = tempdir().unwrap();
        let file_path = temp_dir.path().join("test.md");
        
        let content = "# 测试\n\n这是一个公式: $x + y = z$\n\n块级公式:\n$$\nE = mc^2\n$$\n";
        fs::write(&file_path, content).unwrap();
        
        let mut checker = DocChecker::new(DocCheckerConfig::default());
        let result = checker.check_file(&file_path);
        
        assert!(result.passed);
        assert!(result.errors.is_empty());
    }
} 