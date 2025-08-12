use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::io::{self, Write};
use std::time::Instant;

// 导入我们的工具模块
mod terminology_fixer;
mod structure_checker;

use terminology_fixer::{TerminologyFixer, FixResult};
use structure_checker::{StructureChecker, StructureReport};

#[derive(Debug)]
pub struct BatchFixResult {
    pub terminology_results: Vec<FixResult>,
    pub structure_results: Vec<StructureReport>,
    pub execution_time: std::time::Duration,
    pub success: bool,
}

pub struct BatchFixExecutor {
    pub terminology_fixer: TerminologyFixer,
    pub structure_checker: StructureChecker,
    pub target_directory: PathBuf,
    pub dry_run: bool,
    pub backup_enabled: bool,
}

impl BatchFixExecutor {
    pub fn new(target_directory: PathBuf) -> Self {
        let mut terminology_fixer = TerminologyFixer::new();
        let structure_checker = StructureChecker::new();
        
        Self {
            terminology_fixer,
            structure_checker,
            target_directory,
            dry_run: false,
            backup_enabled: true,
        }
    }
    
    pub fn set_dry_run(&mut self, dry_run: bool) {
        self.dry_run = dry_run;
        self.terminology_fixer.set_dry_run(dry_run);
    }
    
    pub fn set_backup_enabled(&mut self, backup_enabled: bool) {
        self.backup_enabled = backup_enabled;
        self.terminology_fixer.set_backup_enabled(backup_enabled);
    }
    
    pub fn execute(&self) -> Result<BatchFixResult, io::Error> {
        let start_time = Instant::now();
        
        println!("🚀 开始批量修正执行...");
        println!("目标目录: {}", self.target_directory.display());
        println!("试运行: {}", self.dry_run);
        println!("备份: {}", self.backup_enabled);
        println!();
        
        // 第一步：术语修正
        println!("📝 步骤1: 执行术语标准化...");
        let terminology_results = self.terminology_fixer.fix_directory(&self.target_directory)?;
        
        let terminology_success = terminology_results.iter().filter(|r| r.success).count();
        let terminology_total = terminology_results.len();
        let terminology_replacements: usize = terminology_results.iter().map(|r| r.replacements_made).sum();
        
        println!("✅ 术语修正完成!");
        println!("   处理文件: {}", terminology_total);
        println!("   成功文件: {}", terminology_success);
        println!("   总修正数: {}", terminology_replacements);
        println!();
        
        // 第二步：结构检查
        println!("📋 步骤2: 执行结构检查...");
        let structure_results = self.structure_checker.check_directory(&self.target_directory)?;
        
        let structure_success = structure_results.iter().filter(|r| r.success).count();
        let structure_total = structure_results.len();
        let avg_structure_score: f64 = structure_results.iter()
            .filter(|r| r.success)
            .map(|r| r.structure_score)
            .sum::<f64>() / structure_success.max(1) as f64;
        
        println!("✅ 结构检查完成!");
        println!("   检查文件: {}", structure_total);
        println!("   成功文件: {}", structure_success);
        println!("   平均结构分数: {:.2}/100", avg_structure_score);
        println!();
        
        let execution_time = start_time.elapsed();
        
        println!("🎉 批量修正执行完成!");
        println!("   总执行时间: {:.2}秒", execution_time.as_secs_f64());
        println!("   术语修正率: {:.2}%", 
            if terminology_total > 0 { terminology_success as f64 / terminology_total as f64 * 100.0 } else { 0.0 });
        println!("   结构检查率: {:.2}%", 
            if structure_total > 0 { structure_success as f64 / structure_total as f64 * 100.0 } else { 0.0 });
        
        Ok(BatchFixResult {
            terminology_results,
            structure_results,
            execution_time,
            success: true,
        })
    }
    
    pub fn generate_comprehensive_report(&self, result: &BatchFixResult) -> String {
        let mut report = String::new();
        
        report.push_str("# 批量修正综合报告\n\n");
        
        // 执行概览
        report.push_str(&format!("## 执行概览\n"));
        report.push_str(&format!("- **执行时间**: {:.2}秒\n", result.execution_time.as_secs_f64()));
        report.push_str(&format!("- **目标目录**: {}\n", self.target_directory.display()));
        report.push_str(&format!("- **试运行**: {}\n", self.dry_run));
        report.push_str(&format!("- **备份**: {}\n", self.backup_enabled));
        report.push_str(&format!("- **执行状态**: {}\n\n", if result.success { "成功" } else { "失败" }));
        
        // 术语修正结果
        let terminology_total = result.terminology_results.len();
        let terminology_success = result.terminology_results.iter().filter(|r| r.success).count();
        let terminology_replacements: usize = result.terminology_results.iter().map(|r| r.replacements_made).sum();
        let terminology_total_terms: usize = result.terminology_results.iter().map(|r| r.total_terms).sum();
        
        report.push_str(&format!("## 术语修正结果\n"));
        report.push_str(&format!("- **处理文件数**: {}\n", terminology_total));
        report.push_str(&format!("- **成功文件数**: {}\n", terminology_success));
        report.push_str(&format!("- **失败文件数**: {}\n", terminology_total - terminology_success));
        report.push_str(&format!("- **总修正数**: {}\n", terminology_replacements));
        report.push_str(&format!("- **总术语数**: {}\n", terminology_total_terms));
        report.push_str(&format!("- **修正率**: {:.2}%\n\n", 
            if terminology_total_terms > 0 { terminology_replacements as f64 / terminology_total_terms as f64 * 100.0 } else { 0.0 }));
        
        // 结构检查结果
        let structure_total = result.structure_results.len();
        let structure_success = result.structure_results.iter().filter(|r| r.success).count();
        let avg_structure_score: f64 = result.structure_results.iter()
            .filter(|r| r.success)
            .map(|r| r.structure_score)
            .sum::<f64>() / structure_success.max(1) as f64;
        let avg_compliance_rate: f64 = result.structure_results.iter()
            .filter(|r| r.success)
            .map(|r| r.compliance_rate)
            .sum::<f64>() / structure_success.max(1) as f64;
        
        report.push_str(&format!("## 结构检查结果\n"));
        report.push_str(&format!("- **检查文件数**: {}\n", structure_total));
        report.push_str(&format!("- **成功文件数**: {}\n", structure_success));
        report.push_str(&format!("- **失败文件数**: {}\n", structure_total - structure_success));
        report.push_str(&format!("- **平均结构分数**: {:.2}/100\n", avg_structure_score));
        report.push_str(&format!("- **平均合规率**: {:.2}%\n\n", avg_compliance_rate));
        
        // 分数分布
        let excellent = result.structure_results.iter().filter(|r| r.success && r.structure_score >= 90.0).count();
        let good = result.structure_results.iter().filter(|r| r.success && r.structure_score >= 80.0 && r.structure_score < 90.0).count();
        let fair = result.structure_results.iter().filter(|r| r.success && r.structure_score >= 70.0 && r.structure_score < 80.0).count();
        let poor = result.structure_results.iter().filter(|r| r.success && r.structure_score < 70.0).count();
        
        report.push_str(&format!("## 结构分数分布\n"));
        report.push_str(&format!("- **优秀 (90+)**: {}个 ({:.1}%)\n", excellent, 
            if structure_success > 0 { excellent as f64 / structure_success as f64 * 100.0 } else { 0.0 }));
        report.push_str(&format!("- **良好 (80-89)**: {}个 ({:.1}%)\n", good, 
            if structure_success > 0 { good as f64 / structure_success as f64 * 100.0 } else { 0.0 }));
        report.push_str(&format!("- **一般 (70-79)**: {}个 ({:.1}%)\n", fair, 
            if structure_success > 0 { fair as f64 / structure_success as f64 * 100.0 } else { 0.0 }));
        report.push_str(&format!("- **需要改进 (<70)**: {}个 ({:.1}%)\n\n", poor, 
            if structure_success > 0 { poor as f64 / structure_success as f64 * 100.0 } else { 0.0 }));
        
        // 详细文件报告
        report.push_str(&format!("## 详细文件报告\n"));
        
        // 术语修正详情
        if !result.terminology_results.is_empty() {
            report.push_str(&format!("### 术语修正详情\n"));
            for fix_result in result.terminology_results.iter().filter(|r| r.success && r.replacements_made > 0) {
                report.push_str(&format!("#### {}\n", fix_result.file_path));
                report.push_str(&format!("- **修正数**: {}\n", fix_result.replacements_made));
                report.push_str(&format!("- **总术语数**: {}\n", fix_result.total_terms));
                report.push_str(&format!("- **修正率**: {:.2}%\n\n", 
                    if fix_result.total_terms > 0 { fix_result.replacements_made as f64 / fix_result.total_terms as f64 * 100.0 } else { 0.0 }));
            }
        }
        
        // 结构检查详情
        if !result.structure_results.is_empty() {
            report.push_str(&format!("### 结构检查详情\n"));
            for structure_result in result.structure_results.iter().filter(|r| r.success) {
                report.push_str(&format!("#### {}\n", structure_result.file_path));
                report.push_str(&format!("- **结构分数**: {:.2}/100\n", structure_result.structure_score));
                report.push_str(&format!("- **合规率**: {:.2}%\n", structure_result.compliance_rate));
                report.push_str(&format!("- **章节数**: {}\n", structure_result.total_sections));
                
                if !structure_result.missing_sections.is_empty() {
                    report.push_str(&format!("- **缺失章节**: {}\n", structure_result.missing_sections.join(", ")));
                }
                
                report.push_str("\n");
            }
        }
        
        // 失败文件
        let failed_terminology: Vec<_> = result.terminology_results.iter().filter(|r| !r.success).collect();
        let failed_structure: Vec<_> = result.structure_results.iter().filter(|r| !r.success).collect();
        
        if !failed_terminology.is_empty() || !failed_structure.is_empty() {
            report.push_str(&format!("## 失败文件\n"));
            
            if !failed_terminology.is_empty() {
                report.push_str(&format!("### 术语修正失败\n"));
                for fix_result in failed_terminology {
                    report.push_str(&format!("- **{}**: {}\n", fix_result.file_path, 
                        fix_result.error_message.as_ref().unwrap_or(&"未知错误".to_string())));
                }
            }
            
            if !failed_structure.is_empty() {
                report.push_str(&format!("### 结构检查失败\n"));
                for structure_result in failed_structure {
                    report.push_str(&format!("- **{}**: {}\n", structure_result.file_path, 
                        structure_result.error_message.as_ref().unwrap_or(&"未知错误".to_string())));
                }
            }
            
            report.push_str("\n");
        }
        
        // 改进建议
        report.push_str(&format!("## 改进建议\n"));
        
        if terminology_replacements > 0 {
            report.push_str(&format!("### 术语标准化\n"));
            report.push_str(&format!("- ✅ 已完成 {} 个术语修正\n", terminology_replacements));
            report.push_str(&format!("- 📈 术语一致性显著提升\n"));
            report.push_str(&format!("- 🔄 建议建立持续监控机制\n\n"));
        }
        
        if avg_structure_score < 80.0 {
            report.push_str(&format!("### 结构标准化\n"));
            report.push_str(&format!("- ⚠️ 平均结构分数较低 ({:.2}/100)\n", avg_structure_score));
            report.push_str(&format!("- 📋 建议按标准模板重构文档\n"));
            report.push_str(&format!("- 🎯 重点关注缺失章节的补充\n\n"));
        } else {
            report.push_str(&format!("### 结构标准化\n"));
            report.push_str(&format!("- ✅ 结构分数良好 ({:.2}/100)\n", avg_structure_score));
            report.push_str(&format!("- 📈 文档结构组织合理\n"));
            report.push_str(&format!("- 🔄 建议保持现有标准\n\n"));
        }
        
        // 下一步行动
        report.push_str(&format!("## 下一步行动\n"));
        report.push_str(&format!("1. **验证修正效果**: 检查修正后的文档质量\n"));
        report.push_str(&format!("2. **结构重构**: 对低分文档进行结构重构\n"));
        report.push_str(&format!("3. **质量评估**: 使用质量评估框架进行综合评估\n"));
        report.push_str(&format!("4. **持续改进**: 建立持续监控和改进机制\n"));
        
        report
    }
}

fn main() -> Result<(), io::Error> {
    let args: Vec<String> = std::env::args().collect();
    
    if args.len() < 2 {
        println!("用法: batch_fix_executor <目录路径> [--dry-run] [--no-backup]");
        println!();
        println!("选项:");
        println!("  --dry-run     试运行，不实际修改文件");
        println!("  --no-backup   不创建备份文件");
        return Ok(());
    }
    
    let target_directory = PathBuf::from(&args[1]);
    let dry_run = args.contains(&"--dry-run".to_string());
    let no_backup = args.contains(&"--no-backup".to_string());
    
    if !target_directory.exists() {
        eprintln!("错误: 目录不存在: {}", target_directory.display());
        return Ok(());
    }
    
    let mut executor = BatchFixExecutor::new(target_directory);
    executor.set_dry_run(dry_run);
    executor.set_backup_enabled(!no_backup);
    
    // 执行批量修正
    let result = executor.execute()?;
    
    // 生成综合报告
    let report = executor.generate_comprehensive_report(&result);
    
    // 保存报告
    let report_path = executor.target_directory.join("batch_fix_comprehensive_report.md");
    fs::write(&report_path, &report)?;
    
    println!();
    println!("📊 综合报告已保存: {}", report_path.display());
    println!("🎯 批量修正执行完成！");
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::tempdir;
    
    #[test]
    fn test_batch_fix_executor() {
        let temp_dir = tempdir().unwrap();
        let test_file = temp_dir.path().join("test.md");
        
        // 创建测试文件
        let test_content = r#"
# 测试文档

## 特性分析
Rust的trait特性非常强大。

## 所有权系统
变量的拥有权管理是Rust的核心。

## 并发编程
Rust的并发性模型很优秀。
"#;
        
        fs::write(&test_file, test_content).unwrap();
        
        // 创建执行器
        let mut executor = BatchFixExecutor::new(temp_dir.path().to_path_buf());
        executor.set_dry_run(true); // 试运行
        
        // 执行批量修正
        let result = executor.execute().unwrap();
        
        // 验证结果
        assert!(result.success);
        assert!(!result.terminology_results.is_empty());
        assert!(!result.structure_results.is_empty());
        
        // 验证术语修正
        let terminology_success = result.terminology_results.iter().filter(|r| r.success).count();
        assert!(terminology_success > 0);
        
        // 验证结构检查
        let structure_success = result.structure_results.iter().filter(|r| r.success).count();
        assert!(structure_success > 0);
    }
} 