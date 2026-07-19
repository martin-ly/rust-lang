use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use regex::Regex;
use serde::{Deserialize, Serialize};

/// 符号定义
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Symbol {
    pub symbol: String,
    pub meaning: String,
    pub example: String,
    pub category: String,
}

/// 符号使用实例
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SymbolUsage {
    pub symbol: String,
    pub file: PathBuf,
    pub line: usize,
    pub context: String,
    pub expected: Option<String>,
}

/// 符号一致性检查器
pub struct SymbolChecker {
    pub symbols: HashMap<String, Symbol>,
    pub usage_patterns: Vec<Regex>,
    pub violations: Vec<SymbolUsage>,
}

impl SymbolChecker {
    /// 创建新的符号检查器
    pub fn new() -> Self {
        let mut checker = SymbolChecker {
            symbols: HashMap::new(),
            usage_patterns: Vec::new(),
            violations: Vec::new(),
        };
        
        // 初始化统一符号系统
        checker.init_symbols();
        checker.init_patterns();
        
        checker
    }
    
    /// 初始化统一符号系统
    fn init_symbols(&mut self) {
        // 基础集合符号
        self.symbols.insert("𝕋".to_string(), Symbol {
            symbol: "𝕋".to_string(),
            meaning: "类型集合".to_string(),
            example: "t ∈ 𝕋".to_string(),
            category: "基础集合".to_string(),
        });
        
        self.symbols.insert("𝕍".to_string(), Symbol {
            symbol: "𝕍".to_string(),
            meaning: "值集合".to_string(),
            example: "v ∈ 𝕍".to_string(),
            category: "基础集合".to_string(),
        });
        
        self.symbols.insert("𝕏".to_string(), Symbol {
            symbol: "𝕏".to_string(),
            meaning: "变量集合".to_string(),
            example: "x ∈ 𝕏".to_string(),
            category: "基础集合".to_string(),
        });
        
        self.symbols.insert("ℒ".to_string(), Symbol {
            symbol: "ℒ".to_string(),
            meaning: "生命周期集合".to_string(),
            example: "α ∈ ℒ".to_string(),
            category: "基础集合".to_string(),
        });
        
        // 类型系统符号
        self.symbols.insert("⊢".to_string(), Symbol {
            symbol: "⊢".to_string(),
            meaning: "类型判断".to_string(),
            example: "Γ ⊢ e : T".to_string(),
            category: "类型系统".to_string(),
        });
        
        self.symbols.insert("<:".to_string(), Symbol {
            symbol: "<:".to_string(),
            meaning: "子类型关系".to_string(),
            example: "T <: U".to_string(),
            category: "类型系统".to_string(),
        });
        
        self.symbols.insert("∀".to_string(), Symbol {
            symbol: "∀".to_string(),
            meaning: "全称量词".to_string(),
            example: "∀α. T".to_string(),
            category: "逻辑符号".to_string(),
        });
        
        self.symbols.insert("∃".to_string(), Symbol {
            symbol: "∃".to_string(),
            meaning: "存在量词".to_string(),
            example: "∃α. T".to_string(),
            category: "逻辑符号".to_string(),
        });
        
        // 所有权系统符号
        self.symbols.insert("Own".to_string(), Symbol {
            symbol: "Own".to_string(),
            meaning: "所有权关系".to_string(),
            example: "Own(x, v)".to_string(),
            category: "所有权系统".to_string(),
        });
        
        self.symbols.insert("Borrow".to_string(), Symbol {
            symbol: "Borrow".to_string(),
            meaning: "借用关系".to_string(),
            example: "Borrow(r, x, α)".to_string(),
            category: "所有权系统".to_string(),
        });
        
        self.symbols.insert("Move".to_string(), Symbol {
            symbol: "Move".to_string(),
            meaning: "所有权移动".to_string(),
            example: "Move(x → y)".to_string(),
            category: "所有权系统".to_string(),
        });
        
        // 逻辑符号
        self.symbols.insert("⟹".to_string(), Symbol {
            symbol: "⟹".to_string(),
            meaning: "蕴含".to_string(),
            example: "P ⟹ Q".to_string(),
            category: "逻辑符号".to_string(),
        });
        
        self.symbols.insert("⟺".to_string(), Symbol {
            symbol: "⟺".to_string(),
            meaning: "等价".to_string(),
            example: "P ⟺ Q".to_string(),
            category: "逻辑符号".to_string(),
        });
        
        self.symbols.insert("∧".to_string(), Symbol {
            symbol: "∧".to_string(),
            meaning: "逻辑与".to_string(),
            example: "P ∧ Q".to_string(),
            category: "逻辑符号".to_string(),
        });
        
        self.symbols.insert("∨".to_string(), Symbol {
            symbol: "∨".to_string(),
            meaning: "逻辑或".to_string(),
            example: "P ∨ Q".to_string(),
            category: "逻辑符号".to_string(),
        });
        
        self.symbols.insert("¬".to_string(), Symbol {
            symbol: "¬".to_string(),
            meaning: "逻辑非".to_string(),
            example: "¬P".to_string(),
            category: "逻辑符号".to_string(),
        });
        
        // 操作语义符号
        self.symbols.insert("⇓".to_string(), Symbol {
            symbol: "⇓".to_string(),
            meaning: "求值关系".to_string(),
            example: "e ⇓ v".to_string(),
            category: "操作语义".to_string(),
        });
        
        self.symbols.insert("⊥".to_string(), Symbol {
            symbol: "⊥".to_string(),
            meaning: "错误或矛盾".to_string(),
            example: "e ⇓ ⊥".to_string(),
            category: "操作语义".to_string(),
        });
    }
    
    /// 初始化使用模式
    fn init_patterns(&mut self) {
        // 匹配数学符号的模式
        let patterns = vec![
            r"𝕋|𝕍|𝕏|ℒ", // 基础集合符号
            r"⊢|<:|∀|∃", // 类型系统符号
            r"Own|Borrow|Move", // 所有权系统符号
            r"⟹|⟺|∧|∨|¬", // 逻辑符号
            r"⇓|⊥", // 操作语义符号
        ];
        
        for pattern in patterns {
            if let Ok(regex) = Regex::new(pattern) {
                self.usage_patterns.push(regex);
            }
        }
    }
    
    /// 检查单个文件
    pub fn check_file(&mut self, path: &Path) -> Result<(), Box<dyn std::error::Error>> {
        let content = fs::read_to_string(path)?;
        let lines: Vec<&str> = content.lines().collect();
        
        for (line_num, line) in lines.iter().enumerate() {
            self.check_line(path, line_num + 1, line);
        }
        
        Ok(())
    }
    
    /// 检查单行内容
    fn check_line(&mut self, file: &Path, line_num: usize, line: &str) {
        for pattern in &self.usage_patterns {
            for mat in pattern.find_iter(line) {
                let symbol = mat.as_str();
                
                // 检查符号是否在统一符号系统中
                if !self.symbols.contains_key(symbol) {
                    self.violations.push(SymbolUsage {
                        symbol: symbol.to_string(),
                        file: file.to_path_buf(),
                        line: line_num,
                        context: line.to_string(),
                        expected: None,
                    });
                }
            }
        }
    }
    
    /// 检查目录中的所有Markdown文件
    pub fn check_directory(&mut self, dir: &Path) -> Result<(), Box<dyn std::error::Error>> {
        self.violations.clear();
        
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            
            if path.is_file() && path.extension().map_or(false, |ext| ext == "md") {
                self.check_file(&path)?;
            } else if path.is_dir() {
                self.check_directory(&path)?;
            }
        }
        
        Ok(())
    }
    
    /// 生成检查报告
    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        
        report.push_str("# 符号一致性检查报告\n\n");
        report.push_str(&format!("检查时间: {}\n", chrono::Utc::now()));
        report.push_str(&format!("发现违规: {}\n\n", self.violations.len()));
        
        if self.violations.is_empty() {
            report.push_str("✅ 所有符号使用都符合统一符号系统！\n");
        } else {
            report.push_str("## 发现的违规\n\n");
            
            for violation in &self.violations {
                report.push_str(&format!("### 文件: {}\n", violation.file.display()));
                report.push_str(&format!("行号: {}\n", violation.line));
                report.push_str(&format!("符号: `{}`\n", violation.symbol));
                report.push_str(&format!("上下文: `{}`\n", violation.context));
                report.push_str("\n");
            }
            
            report.push_str("## 建议\n\n");
            report.push_str("1. 检查上述符号是否应该使用统一符号系统中的符号\n");
            report.push_str("2. 如果符号不在统一系统中，考虑添加到符号系统或使用替代符号\n");
            report.push_str("3. 确保所有文档中的符号使用保持一致\n");
        }
        
        report
    }
    
    /// 导出符号系统
    pub fn export_symbols(&self) -> String {
        let mut export = String::new();
        
        export.push_str("# Rust形式化理论统一符号系统\n\n");
        
        // 按类别分组
        let mut categories: HashMap<String, Vec<&Symbol>> = HashMap::new();
        for symbol in self.symbols.values() {
            categories.entry(symbol.category.clone()).or_insert_with(Vec::new).push(symbol);
        }
        
        for (category, symbols) in categories {
            export.push_str(&format!("## {}\n\n", category));
            export.push_str("| 符号 | 含义 | 示例 |\n");
            export.push_str("|------|------|------|\n");
            
            for symbol in symbols {
                export.push_str(&format!("| `{}` | {} | `{}` |\n", 
                    symbol.symbol, symbol.meaning, symbol.example));
            }
            
            export.push_str("\n");
        }
        
        export
    }
}

/// 命令行接口
pub struct Cli {
    pub command: String,
    pub path: PathBuf,
    pub output: Option<PathBuf>,
}

impl Cli {
    pub fn parse_args() -> Result<Self, Box<dyn std::error::Error>> {
        let args: Vec<String> = std::env::args().collect();
        
        if args.len() < 3 {
            return Err("用法: symbol_checker <command> <path> [output]".into());
        }
        
        let command = args[1].clone();
        let path = PathBuf::from(&args[2]);
        let output = args.get(3).map(|s| PathBuf::from(s));
        
        Ok(Cli { command, path, output })
    }
    
    pub fn run(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut checker = SymbolChecker::new();
        
        match self.command.as_str() {
            "check" => {
                if self.path.is_file() {
                    checker.check_file(&self.path)?;
                } else {
                    checker.check_directory(&self.path)?;
                }
                
                let report = checker.generate_report();
                
                if let Some(output_path) = &self.output {
                    fs::write(output_path, report)?;
                    println!("报告已保存到: {}", output_path.display());
                } else {
                    println!("{}", report);
                }
            }
            
            "export" => {
                let symbols = checker.export_symbols();
                
                if let Some(output_path) = &self.output {
                    fs::write(output_path, symbols)?;
                    println!("符号系统已导出到: {}", output_path.display());
                } else {
                    println!("{}", symbols);
                }
            }
            
            _ => {
                return Err(format!("未知命令: {}", self.command).into());
            }
        }
        
        Ok(())
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse_args()?;
    cli.run()
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;
    use std::fs;
    
    #[test]
    fn test_symbol_checker_creation() {
        let checker = SymbolChecker::new();
        assert!(!checker.symbols.is_empty());
        assert!(!checker.usage_patterns.is_empty());
    }
    
    #[test]
    fn test_symbol_validation() {
        let checker = SymbolChecker::new();
        
        // 测试有效符号
        assert!(checker.symbols.contains_key("𝕋"));
        assert!(checker.symbols.contains_key("⊢"));
        assert!(checker.symbols.contains_key("Own"));
        
        // 测试无效符号
        assert!(!checker.symbols.contains_key("invalid_symbol"));
    }
    
    #[test]
    fn test_file_checking() {
        let mut checker = SymbolChecker::new();
        let temp_dir = tempdir().unwrap();
        let test_file = temp_dir.path().join("test.md");
        
        // 创建测试文件
        let content = r#"
# 测试文档

这里使用了正确的符号: Γ ⊢ e : T
这里使用了错误的符号: invalid_symbol

更多正确符号: Own(x, v), Borrow(r, x, α)
"#;
        
        fs::write(&test_file, content).unwrap();
        
        // 检查文件
        checker.check_file(&test_file).unwrap();
        
        // 应该发现一个违规
        assert_eq!(checker.violations.len(), 1);
        assert_eq!(checker.violations[0].symbol, "invalid_symbol");
    }
    
    #[test]
    fn test_report_generation() {
        let mut checker = SymbolChecker::new();
        let temp_dir = tempdir().unwrap();
        let test_file = temp_dir.path().join("test.md");
        
        // 创建包含违规的测试文件
        let content = "使用错误符号: wrong_symbol";
        fs::write(&test_file, content).unwrap();
        
        checker.check_file(&test_file).unwrap();
        let report = checker.generate_report();
        
        assert!(report.contains("发现的违规"));
        assert!(report.contains("wrong_symbol"));
    }
} 