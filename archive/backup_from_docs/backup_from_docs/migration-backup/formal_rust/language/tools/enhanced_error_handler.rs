use std::collections::HashMap;
use std::fmt;

/// 增强的错误处理系统
pub struct ErrorHandler {
    pub error_classifier: ErrorClassifier,
    pub error_reporter: ErrorReporter,
    pub fix_suggester: FixSuggester,
    pub error_analyzer: ErrorAnalyzer,
    pub error_tracker: ErrorTracker,
}

impl ErrorHandler {
    pub fn new() -> Self {
        Self {
            error_classifier: ErrorClassifier::new(),
            error_reporter: ErrorReporter::new(),
            fix_suggester: FixSuggester::new(),
            error_analyzer: ErrorAnalyzer::new(),
            error_tracker: ErrorTracker::new(),
        }
    }

    /// 处理错误
    pub fn handle_error(&self, error: &Error) -> ErrorReport {
        // 错误分类
        let classification = self.error_classifier.classify(error);
        
        // 错误分析
        let analysis = self.error_analyzer.analyze(error, &classification);
        
        // 详细报告
        let report = self.error_reporter.generate_report(error, &classification, &analysis);
        
        // 修复建议
        let suggestions = self.fix_suggester.suggest_fixes(error, &classification, &analysis);
        
        // 错误追踪
        self.error_tracker.track_error(error, &classification);
        
        ErrorReport {
            error: error.clone(),
            classification,
            analysis,
            report,
            suggestions,
            timestamp: std::time::SystemTime::now(),
        }
    }

    /// 批量处理错误
    pub fn handle_errors_batch(&self, errors: &[Error]) -> BatchErrorReport {
        let mut individual_reports = Vec::new();
        let mut global_analysis = GlobalErrorAnalysis::new();
        
        for error in errors {
            let report = self.handle_error(error);
            individual_reports.push(report.clone());
            
            // 更新全局分析
            global_analysis.update(&report);
        }
        
        BatchErrorReport {
            individual_reports,
            global_analysis,
            summary: self.generate_batch_summary(&individual_reports),
        }
    }

    /// 生成批量摘要
    fn generate_batch_summary(&self, reports: &[ErrorReport]) -> ErrorSummary {
        let total_errors = reports.len();
        let mut by_severity = HashMap::new();
        let mut by_category = HashMap::new();
        let mut by_source = HashMap::new();
        
        for report in reports {
            // 按严重程度统计
            *by_severity.entry(report.classification.severity.clone()).or_insert(0) += 1;
            
            // 按类别统计
            *by_category.entry(report.classification.category.clone()).or_insert(0) += 1;
            
            // 按来源统计
            *by_source.entry(report.error.source.clone()).or_insert(0) += 1;
        }
        
        ErrorSummary {
            total_errors,
            by_severity,
            by_category,
            by_source,
            most_common_errors: self.find_most_common_errors(reports),
        }
    }

    /// 查找最常见错误
    fn find_most_common_errors(&self, reports: &[ErrorReport]) -> Vec<CommonError> {
        let mut error_counts = HashMap::new();
        
        for report in reports {
            let key = format!("{}:{}", report.error.error_type, report.error.message);
            *error_counts.entry(key).or_insert(0) += 1;
        }
        
        let mut common_errors: Vec<CommonError> = error_counts
            .into_iter()
            .map(|(error, count)| CommonError {
                error_pattern: error,
                count,
                percentage: count as f64 / reports.len() as f64,
            })
            .collect();
        
        common_errors.sort_by(|a, b| b.count.cmp(&a.count));
        common_errors.truncate(10); // 只保留前10个
        common_errors
    }
}

/// 错误分类器
pub struct ErrorClassifier {
    pub classification_rules: Vec<ClassificationRule>,
    pub severity_analyzer: SeverityAnalyzer,
    pub category_detector: CategoryDetector,
}

impl ErrorClassifier {
    pub fn new() -> Self {
        Self {
            classification_rules: vec![
                ClassificationRule::Syntax,
                ClassificationRule::Semantic,
                ClassificationRule::Type,
                ClassificationRule::Logic,
                ClassificationRule::Performance,
                ClassificationRule::Security,
            ],
            severity_analyzer: SeverityAnalyzer::new(),
            category_detector: CategoryDetector::new(),
        }
    }

    pub fn classify(&self, error: &Error) -> ErrorClassification {
        // 确定严重程度
        let severity = self.severity_analyzer.analyze(error);
        
        // 确定类别
        let category = self.category_detector.detect(error);
        
        // 应用分类规则
        let mut tags = Vec::new();
        for rule in &self.classification_rules {
            if self.apply_classification_rule(error, rule) {
                tags.push(rule.clone());
            }
        }
        
        ErrorClassification {
            severity,
            category,
            tags,
            confidence: self.calculate_confidence(error, &severity, &category),
        }
    }

    fn apply_classification_rule(&self, error: &Error, rule: &ClassificationRule) -> bool {
        match rule {
            ClassificationRule::Syntax => self.is_syntax_error(error),
            ClassificationRule::Semantic => self.is_semantic_error(error),
            ClassificationRule::Type => self.is_type_error(error),
            ClassificationRule::Logic => self.is_logic_error(error),
            ClassificationRule::Performance => self.is_performance_error(error),
            ClassificationRule::Security => self.is_security_error(error),
        }
    }

    fn is_syntax_error(&self, error: &Error) -> bool {
        error.message.contains("syntax") || 
        error.message.contains("expected") ||
        error.message.contains("unexpected")
    }

    fn is_semantic_error(&self, error: &Error) -> bool {
        error.message.contains("semantic") ||
        error.message.contains("meaning") ||
        error.message.contains("interpretation")
    }

    fn is_type_error(&self, error: &Error) -> bool {
        error.message.contains("type") ||
        error.message.contains("mismatch") ||
        error.message.contains("expected type")
    }

    fn is_logic_error(&self, error: &Error) -> bool {
        error.message.contains("logic") ||
        error.message.contains("reasoning") ||
        error.message.contains("inference")
    }

    fn is_performance_error(&self, error: &Error) -> bool {
        error.message.contains("performance") ||
        error.message.contains("efficiency") ||
        error.message.contains("optimization")
    }

    fn is_security_error(&self, error: &Error) -> bool {
        error.message.contains("security") ||
        error.message.contains("vulnerability") ||
        error.message.contains("unsafe")
    }

    fn calculate_confidence(&self, error: &Error, severity: &ErrorSeverity, category: &ErrorCategory) -> f64 {
        let mut confidence = 0.0;
        let mut factors = 0;
        
        // 基于错误消息的置信度
        if !error.message.is_empty() {
            confidence += 0.3;
            factors += 1;
        }
        
        // 基于错误类型的置信度
        if !error.error_type.is_empty() {
            confidence += 0.3;
            factors += 1;
        }
        
        // 基于严重程度的置信度
        match severity {
            ErrorSeverity::Critical => confidence += 0.2,
            ErrorSeverity::Error => confidence += 0.15,
            ErrorSeverity::Warning => confidence += 0.1,
            ErrorSeverity::Info => confidence += 0.05,
        }
        factors += 1;
        
        // 基于类别的置信度
        if category != &ErrorCategory::Unknown {
            confidence += 0.2;
            factors += 1;
        }
        
        if factors > 0 {
            confidence / factors as f64
        } else {
            0.0
        }
    }
}

/// 错误报告器
pub struct ErrorReporter {
    pub report_templates: HashMap<ErrorCategory, ReportTemplate>,
    pub detail_generator: DetailGenerator,
    pub context_provider: ContextProvider,
}

impl ErrorReporter {
    pub fn new() -> Self {
        let mut templates = HashMap::new();
        templates.insert(ErrorCategory::Syntax, ReportTemplate::new("语法错误报告"));
        templates.insert(ErrorCategory::Semantic, ReportTemplate::new("语义错误报告"));
        templates.insert(ErrorCategory::Type, ReportTemplate::new("类型错误报告"));
        templates.insert(ErrorCategory::Logic, ReportTemplate::new("逻辑错误报告"));
        templates.insert(ErrorCategory::Performance, ReportTemplate::new("性能错误报告"));
        templates.insert(ErrorCategory::Security, ReportTemplate::new("安全错误报告"));
        
        Self {
            report_templates: templates,
            detail_generator: DetailGenerator::new(),
            context_provider: ContextProvider::new(),
        }
    }

    pub fn generate_report(&self, error: &Error, classification: &ErrorClassification, analysis: &ErrorAnalysis) -> DetailedReport {
        // 获取报告模板
        let template = self.report_templates.get(&classification.category)
            .unwrap_or(&ReportTemplate::new("通用错误报告"));
        
        // 生成详细信息
        let details = self.detail_generator.generate(error, classification);
        
        // 提供上下文信息
        let context = self.context_provider.provide(error);
        
        // 生成报告内容
        let content = self.generate_report_content(error, classification, analysis, &details, &context);
        
        DetailedReport {
            template: template.clone(),
            content,
            details,
            context,
            timestamp: std::time::SystemTime::now(),
        }
    }

    fn generate_report_content(&self, error: &Error, classification: &ErrorClassification, analysis: &ErrorAnalysis, details: &ErrorDetails, context: &ErrorContext) -> String {
        format!(
            "错误报告\n\
            ==========\n\
            错误类型: {}\n\
            严重程度: {:?}\n\
            类别: {:?}\n\
            消息: {}\n\
            位置: {}\n\
            来源: {}\n\
            \n详细信息:\n{}\n\
            \n上下文:\n{}\n\
            \n分析:\n{}\n\
            \n置信度: {:.2}",
            error.error_type,
            classification.severity,
            classification.category,
            error.message,
            error.location,
            error.source,
            details.content,
            context.description,
            analysis.summary,
            classification.confidence
        )
    }
}

/// 修复建议器
pub struct FixSuggester {
    pub fix_patterns: HashMap<ErrorCategory, Vec<FixPattern>>,
    pub code_generator: CodeGenerator,
    pub fix_validator: FixValidator,
}

impl FixSuggester {
    pub fn new() -> Self {
        let mut patterns = HashMap::new();
        
        // 语法错误修复模式
        patterns.insert(ErrorCategory::Syntax, vec![
            FixPattern::new("添加缺失的分号", "在行末添加 ;"),
            FixPattern::new("修复括号匹配", "检查并修复括号匹配"),
            FixPattern::new("修复引号", "检查并修复引号匹配"),
        ]);
        
        // 类型错误修复模式
        patterns.insert(ErrorCategory::Type, vec![
            FixPattern::new("添加类型注解", "为变量添加明确的类型注解"),
            FixPattern::new("修复类型不匹配", "确保类型匹配"),
            FixPattern::new("使用正确的类型", "使用正确的类型定义"),
        ]);
        
        // 语义错误修复模式
        patterns.insert(ErrorCategory::Semantic, vec![
            FixPattern::new("修复变量作用域", "确保变量在正确的作用域中"),
            FixPattern::new("修复生命周期", "确保生命周期正确"),
            FixPattern::new("修复借用规则", "遵循Rust借用规则"),
        ]);
        
        Self {
            fix_patterns,
            code_generator: CodeGenerator::new(),
            fix_validator: FixValidator::new(),
        }
    }

    pub fn suggest_fixes(&self, error: &Error, classification: &ErrorClassification, analysis: &ErrorAnalysis) -> Vec<FixSuggestion> {
        let mut suggestions = Vec::new();
        
        // 获取适用的修复模式
        if let Some(patterns) = self.fix_patterns.get(&classification.category) {
            for pattern in patterns {
                if self.is_pattern_applicable(error, pattern) {
                    let fix_code = self.code_generator.generate_fix(error, pattern);
                    let validation = self.fix_validator.validate_fix(&fix_code, error);
                    
                    suggestions.push(FixSuggestion {
                        pattern: pattern.clone(),
                        code: fix_code,
                        validation,
                        confidence: self.calculate_fix_confidence(error, pattern, &validation),
                    });
                }
            }
        }
        
        // 按置信度排序
        suggestions.sort_by(|a, b| b.confidence.partial_cmp(&a.confidence).unwrap());
        suggestions
    }

    fn is_pattern_applicable(&self, error: &Error, pattern: &FixPattern) -> bool {
        // 检查模式是否适用于错误
        error.message.contains(&pattern.keywords) ||
        error.error_type.contains(&pattern.keywords)
    }

    fn calculate_fix_confidence(&self, error: &Error, pattern: &FixPattern, validation: &FixValidation) -> f64 {
        let mut confidence = 0.0;
        let mut factors = 0;
        
        // 基于模式匹配的置信度
        if self.is_pattern_applicable(error, pattern) {
            confidence += 0.4;
            factors += 1;
        }
        
        // 基于验证结果的置信度
        match validation.status {
            FixValidationStatus::Valid => {
                confidence += 0.4;
                factors += 1;
            }
            FixValidationStatus::Warning => {
                confidence += 0.2;
                factors += 1;
            }
            FixValidationStatus::Invalid => {
                confidence += 0.0;
                factors += 1;
            }
        }
        
        // 基于错误严重程度的置信度
        match error.severity {
            ErrorSeverity::Critical => confidence += 0.2,
            ErrorSeverity::Error => confidence += 0.15,
            ErrorSeverity::Warning => confidence += 0.1,
            ErrorSeverity::Info => confidence += 0.05,
        }
        factors += 1;
        
        if factors > 0 {
            confidence / factors as f64
        } else {
            0.0
        }
    }
}

/// 错误分析器
pub struct ErrorAnalyzer {
    pub analysis_rules: Vec<AnalysisRule>,
    pub pattern_matcher: PatternMatcher,
    pub impact_analyzer: ImpactAnalyzer,
}

impl ErrorAnalyzer {
    pub fn new() -> Self {
        Self {
            analysis_rules: vec![
                AnalysisRule::RootCause,
                AnalysisRule::Impact,
                AnalysisRule::Pattern,
                AnalysisRule::Context,
            ],
            pattern_matcher: PatternMatcher::new(),
            impact_analyzer: ImpactAnalyzer::new(),
        }
    }

    pub fn analyze(&self, error: &Error, classification: &ErrorClassification) -> ErrorAnalysis {
        let mut analysis_results = Vec::new();
        
        // 应用分析规则
        for rule in &self.analysis_rules {
            if let Some(result) = self.apply_analysis_rule(error, classification, rule) {
                analysis_results.push(result);
            }
        }
        
        // 模式匹配
        let patterns = self.pattern_matcher.match_patterns(error);
        
        // 影响分析
        let impact = self.impact_analyzer.analyze_impact(error, classification);
        
        ErrorAnalysis {
            results: analysis_results,
            patterns,
            impact,
            summary: self.generate_analysis_summary(&analysis_results, &patterns, &impact),
        }
    }

    fn apply_analysis_rule(&self, error: &Error, classification: &ErrorClassification, rule: &AnalysisRule) -> Option<AnalysisResult> {
        match rule {
            AnalysisRule::RootCause => self.analyze_root_cause(error),
            AnalysisRule::Impact => self.analyze_impact(error),
            AnalysisRule::Pattern => self.analyze_pattern(error),
            AnalysisRule::Context => self.analyze_context(error),
        }
    }

    fn analyze_root_cause(&self, error: &Error) -> Option<AnalysisResult> {
        // 分析根本原因
        let root_cause = self.determine_root_cause(error);
        Some(AnalysisResult::RootCause(root_cause))
    }

    fn analyze_impact(&self, error: &Error) -> Option<AnalysisResult> {
        // 分析影响
        let impact = self.determine_impact(error);
        Some(AnalysisResult::Impact(impact))
    }

    fn analyze_pattern(&self, error: &Error) -> Option<AnalysisResult> {
        // 分析模式
        let pattern = self.determine_pattern(error);
        Some(AnalysisResult::Pattern(pattern))
    }

    fn analyze_context(&self, error: &Error) -> Option<AnalysisResult> {
        // 分析上下文
        let context = self.determine_context(error);
        Some(AnalysisResult::Context(context))
    }

    fn determine_root_cause(&self, error: &Error) -> String {
        // 确定根本原因
        if error.message.contains("syntax") {
            "语法错误导致编译失败".to_string()
        } else if error.message.contains("type") {
            "类型系统错误导致类型检查失败".to_string()
        } else if error.message.contains("borrow") {
            "借用检查器错误导致内存安全违规".to_string()
        } else {
            "未知根本原因".to_string()
        }
    }

    fn determine_impact(&self, error: &Error) -> String {
        // 确定影响
        match error.severity {
            ErrorSeverity::Critical => "严重错误，程序无法运行".to_string(),
            ErrorSeverity::Error => "错误，程序编译失败".to_string(),
            ErrorSeverity::Warning => "警告，可能存在问题".to_string(),
            ErrorSeverity::Info => "信息，仅供参考".to_string(),
        }
    }

    fn determine_pattern(&self, error: &Error) -> String {
        // 确定模式
        if error.message.contains("expected") {
            "期望模式：期望特定语法结构".to_string()
        } else if error.message.contains("mismatch") {
            "不匹配模式：类型或值不匹配".to_string()
        } else if error.message.contains("borrow") {
            "借用模式：违反借用规则".to_string()
        } else {
            "通用模式：一般性错误".to_string()
        }
    }

    fn determine_context(&self, error: &Error) -> String {
        // 确定上下文
        format!("错误发生在 {} 的 {} 位置", error.source, error.location)
    }

    fn generate_analysis_summary(&self, results: &[AnalysisResult], patterns: &[ErrorPattern], impact: &ErrorImpact) -> String {
        format!(
            "分析摘要:\n\
            - 分析结果数量: {}\n\
            - 匹配模式数量: {}\n\
            - 影响级别: {:?}\n\
            - 建议优先级: {:?}",
            results.len(),
            patterns.len(),
            impact.level,
            impact.priority
        )
    }
}

/// 错误追踪器
pub struct ErrorTracker {
    pub error_history: Vec<TrackedError>,
    pub statistics: ErrorStatistics,
    pub trend_analyzer: TrendAnalyzer,
}

impl ErrorTracker {
    pub fn new() -> Self {
        Self {
            error_history: Vec::new(),
            statistics: ErrorStatistics::new(),
            trend_analyzer: TrendAnalyzer::new(),
        }
    }

    pub fn track_error(&mut self, error: &Error, classification: &ErrorClassification) {
        let tracked_error = TrackedError {
            error: error.clone(),
            classification: classification.clone(),
            timestamp: std::time::SystemTime::now(),
        };
        
        self.error_history.push(tracked_error);
        self.statistics.update(&error, classification);
        self.trend_analyzer.update(&error);
    }

    pub fn get_statistics(&self) -> &ErrorStatistics {
        &self.statistics
    }

    pub fn get_trends(&self) -> ErrorTrends {
        self.trend_analyzer.analyze_trends(&self.error_history)
    }
}

// 数据结构定义

#[derive(Debug, Clone)]
pub struct Error {
    pub error_type: String,
    pub message: String,
    pub location: String,
    pub source: String,
    pub severity: ErrorSeverity,
    pub code: Option<String>,
}

#[derive(Debug, Clone)]
pub struct ErrorReport {
    pub error: Error,
    pub classification: ErrorClassification,
    pub analysis: ErrorAnalysis,
    pub report: DetailedReport,
    pub suggestions: Vec<FixSuggestion>,
    pub timestamp: std::time::SystemTime,
}

#[derive(Debug, Clone)]
pub struct BatchErrorReport {
    pub individual_reports: Vec<ErrorReport>,
    pub global_analysis: GlobalErrorAnalysis,
    pub summary: ErrorSummary,
}

#[derive(Debug, Clone)]
pub struct ErrorClassification {
    pub severity: ErrorSeverity,
    pub category: ErrorCategory,
    pub tags: Vec<ClassificationRule>,
    pub confidence: f64,
}

#[derive(Debug, Clone)]
pub struct ErrorAnalysis {
    pub results: Vec<AnalysisResult>,
    pub patterns: Vec<ErrorPattern>,
    pub impact: ErrorImpact,
    pub summary: String,
}

#[derive(Debug, Clone)]
pub struct DetailedReport {
    pub template: ReportTemplate,
    pub content: String,
    pub details: ErrorDetails,
    pub context: ErrorContext,
    pub timestamp: std::time::SystemTime,
}

#[derive(Debug, Clone)]
pub struct FixSuggestion {
    pub pattern: FixPattern,
    pub code: String,
    pub validation: FixValidation,
    pub confidence: f64,
}

#[derive(Debug, Clone)]
pub struct TrackedError {
    pub error: Error,
    pub classification: ErrorClassification,
    pub timestamp: std::time::SystemTime,
}

// 枚举定义

#[derive(Debug, Clone)]
pub enum ErrorSeverity {
    Critical,
    Error,
    Warning,
    Info,
}

#[derive(Debug, Clone)]
pub enum ErrorCategory {
    Syntax,
    Semantic,
    Type,
    Logic,
    Performance,
    Security,
    Unknown,
}

#[derive(Debug, Clone)]
pub enum ClassificationRule {
    Syntax,
    Semantic,
    Type,
    Logic,
    Performance,
    Security,
}

#[derive(Debug, Clone)]
pub enum AnalysisRule {
    RootCause,
    Impact,
    Pattern,
    Context,
}

#[derive(Debug, Clone)]
pub enum AnalysisResult {
    RootCause(String),
    Impact(String),
    Pattern(String),
    Context(String),
}

#[derive(Debug, Clone)]
pub enum FixValidationStatus {
    Valid,
    Warning,
    Invalid,
}

// 占位符结构体

#[derive(Debug, Clone)]
pub struct SeverityAnalyzer;

impl SeverityAnalyzer {
    pub fn new() -> Self {
        Self
    }
}

#[derive(Debug, Clone)]
pub struct CategoryDetector;

impl CategoryDetector {
    pub fn new() -> Self {
        Self
    }
}

#[derive(Debug, Clone)]
pub struct DetailGenerator;

impl DetailGenerator {
    pub fn new() -> Self {
        Self
    }
}

#[derive(Debug, Clone)]
pub struct ContextProvider;

impl ContextProvider {
    pub fn new() -> Self {
        Self
    }
}

#[derive(Debug, Clone)]
pub struct CodeGenerator;

impl CodeGenerator {
    pub fn new() -> Self {
        Self
    }
}

#[derive(Debug, Clone)]
pub struct FixValidator;

impl FixValidator {
    pub fn new() -> Self {
        Self
    }
}

#[derive(Debug, Clone)]
pub struct PatternMatcher;

impl PatternMatcher {
    pub fn new() -> Self {
        Self
    }
}

#[derive(Debug, Clone)]
pub struct ImpactAnalyzer;

impl ImpactAnalyzer {
    pub fn new() -> Self {
        Self
    }
}

#[derive(Debug, Clone)]
pub struct TrendAnalyzer;

impl TrendAnalyzer {
    pub fn new() -> Self {
        Self
    }
}

#[derive(Debug, Clone)]
pub struct ReportTemplate {
    pub name: String,
}

impl ReportTemplate {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ErrorDetails {
    pub content: String,
}

#[derive(Debug, Clone)]
pub struct ErrorContext {
    pub description: String,
}

#[derive(Debug, Clone)]
pub struct FixPattern {
    pub name: String,
    pub description: String,
    pub keywords: String,
}

impl FixPattern {
    pub fn new(name: &str, description: &str) -> Self {
        Self {
            name: name.to_string(),
            description: description.to_string(),
            keywords: name.to_lowercase(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FixValidation {
    pub status: FixValidationStatus,
    pub message: String,
}

#[derive(Debug, Clone)]
pub struct ErrorPattern {
    pub name: String,
    pub description: String,
}

#[derive(Debug, Clone)]
pub struct ErrorImpact {
    pub level: ImpactLevel,
    pub priority: Priority,
}

#[derive(Debug, Clone)]
pub enum ImpactLevel {
    High,
    Medium,
    Low,
}

#[derive(Debug, Clone)]
pub enum Priority {
    High,
    Medium,
    Low,
}

#[derive(Debug, Clone)]
pub struct GlobalErrorAnalysis {
    pub total_errors: usize,
    pub critical_errors: usize,
    pub common_patterns: Vec<String>,
}

impl GlobalErrorAnalysis {
    pub fn new() -> Self {
        Self {
            total_errors: 0,
            critical_errors: 0,
            common_patterns: Vec::new(),
        }
    }

    pub fn update(&mut self, report: &ErrorReport) {
        self.total_errors += 1;
        if matches!(report.classification.severity, ErrorSeverity::Critical) {
            self.critical_errors += 1;
        }
    }
}

#[derive(Debug, Clone)]
pub struct ErrorSummary {
    pub total_errors: usize,
    pub by_severity: HashMap<ErrorSeverity, usize>,
    pub by_category: HashMap<ErrorCategory, usize>,
    pub by_source: HashMap<String, usize>,
    pub most_common_errors: Vec<CommonError>,
}

#[derive(Debug, Clone)]
pub struct CommonError {
    pub error_pattern: String,
    pub count: usize,
    pub percentage: f64,
}

#[derive(Debug, Clone)]
pub struct ErrorStatistics {
    pub total_errors: usize,
    pub by_severity: HashMap<ErrorSeverity, usize>,
    pub by_category: HashMap<ErrorCategory, usize>,
}

impl ErrorStatistics {
    pub fn new() -> Self {
        Self {
            total_errors: 0,
            by_severity: HashMap::new(),
            by_category: HashMap::new(),
        }
    }

    pub fn update(&mut self, error: &Error, classification: &ErrorClassification) {
        self.total_errors += 1;
        *self.by_severity.entry(error.severity.clone()).or_insert(0) += 1;
        *self.by_category.entry(classification.category.clone()).or_insert(0) += 1;
    }
}

#[derive(Debug, Clone)]
pub struct ErrorTrends {
    pub recent_trends: Vec<Trend>,
    pub long_term_trends: Vec<Trend>,
}

#[derive(Debug, Clone)]
pub struct Trend {
    pub pattern: String,
    pub frequency: f64,
    pub direction: TrendDirection,
}

#[derive(Debug, Clone)]
pub enum TrendDirection {
    Increasing,
    Decreasing,
    Stable,
}

impl fmt::Display for ErrorHandler {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Enhanced Error Handler with comprehensive error management")
    }
} 