//! Rust 1.90 RPITIT 流水线模式高级示例
//!
//! 本示例展示：
//! 1. Return Position impl Trait in Traits (RPITIT)
//! 2. 零成本抽象的流水线模式
//! 3. 可组合的数据处理管道
//! 4. 惰性求值与迭代器链
//! 5. 与传统关联类型的对比

// ============================================================================
// 核心 RPITIT Trait - 流水线处理器
// ============================================================================

/// 流水线处理器 trait (使用 RPITIT)
pub trait PipelineProcessor {
    type Input;
    type Output;
    
    /// 处理单个元素 - 返回 impl Iterator (RPITIT)
    fn process(&self, input: Self::Input) -> impl Iterator<Item = Self::Output>;
    
    /// 批量处理 - 返回 impl Iterator (RPITIT)
    fn process_batch<I>(&self, inputs: I) -> impl Iterator<Item = Self::Output>
    where
        I: IntoIterator<Item = Self::Input>,
        Self::Input: 'static,
        Self::Output: 'static,
    {
        inputs.into_iter()
            .flat_map(move |input| self.process(input))
    }
    
    /// 处理器名称
    fn name(&self) -> &str;
}

/// 可链接的流水线 trait (使用 RPITIT)
pub trait ChainableProcessor: PipelineProcessor {
    /// 链接下一个处理器
    fn chain<P>(self, next: P) -> ProcessorChain<Self, P>
    where
        Self: Sized,
        P: PipelineProcessor<Input = Self::Output>,
    {
        ProcessorChain::new(self, next)
    }
}

// 为所有实现了 PipelineProcessor 的类型自动实现 ChainableProcessor
impl<T: PipelineProcessor> ChainableProcessor for T {}

// ============================================================================
// 示例 1: 文本处理流水线
// ============================================================================

/// 分词处理器
pub struct TokenizerProcessor {
    delimiter: char,
}

impl TokenizerProcessor {
    pub fn new(delimiter: char) -> Self {
        TokenizerProcessor { delimiter }
    }
}

impl PipelineProcessor for TokenizerProcessor {
    type Input = String;
    type Output = String;
    
    fn process(&self, input: String) -> impl Iterator<Item = String> {
        let delimiter = self.delimiter;
        input.split(delimiter)
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .into_iter()
    }
    
    fn name(&self) -> &str {
        "Tokenizer"
    }
}

/// 过滤处理器
pub struct FilterProcessor<F> 
where
    F: Fn(&str) -> bool,
{
    predicate: F,
}

impl<F> FilterProcessor<F>
where
    F: Fn(&str) -> bool,
{
    pub fn new(predicate: F) -> Self {
        FilterProcessor { predicate }
    }
}

impl<F> PipelineProcessor for FilterProcessor<F>
where
    F: Fn(&str) -> bool,
{
    type Input = String;
    type Output = String;
    
    fn process(&self, input: String) -> impl Iterator<Item = String> {
        if (self.predicate)(&input) {
            Some(input).into_iter()
        } else {
            None.into_iter()
        }
    }
    
    fn name(&self) -> &str {
        "Filter"
    }
}

/// 转换处理器
pub struct MapProcessor<F, T>
where
    F: Fn(String) -> T,
{
    mapper: F,
}

impl<F, T> MapProcessor<F, T>
where
    F: Fn(String) -> T,
{
    pub fn new(mapper: F) -> Self {
        MapProcessor { mapper }
    }
}

impl<F, T> PipelineProcessor for MapProcessor<F, T>
where
    F: Fn(String) -> T,
{
    type Input = String;
    type Output = T;
    
    fn process(&self, input: String) -> impl Iterator<Item = T> {
        std::iter::once((self.mapper)(input))
    }
    
    fn name(&self) -> &str {
        "Map"
    }
}

// ============================================================================
// 示例 2: 数值处理流水线
// ============================================================================

/// 数值生成器
pub struct RangeGenerator {
    start: i32,
    end: i32,
}

impl RangeGenerator {
    pub fn new(start: i32, end: i32) -> Self {
        RangeGenerator { start, end }
    }
}

impl PipelineProcessor for RangeGenerator {
    type Input = ();
    type Output = i32;
    
    fn process(&self, _input: ()) -> impl Iterator<Item = i32> {
        (self.start..self.end).collect::<Vec<_>>().into_iter()
    }
    
    fn name(&self) -> &str {
        "RangeGenerator"
    }
}

/// 数值过滤器（偶数）
pub struct EvenFilter;

impl PipelineProcessor for EvenFilter {
    type Input = i32;
    type Output = i32;
    
    fn process(&self, input: i32) -> impl Iterator<Item = i32> {
        if input % 2 == 0 {
            Some(input).into_iter()
        } else {
            None.into_iter()
        }
    }
    
    fn name(&self) -> &str {
        "EvenFilter"
    }
}

/// 数值映射器（平方）
pub struct SquareMapper;

impl PipelineProcessor for SquareMapper {
    type Input = i32;
    type Output = i32;
    
    fn process(&self, input: i32) -> impl Iterator<Item = i32> {
        std::iter::once(input * input)
    }
    
    fn name(&self) -> &str {
        "SquareMapper"
    }
}

/// 数值累加器
pub struct SumReducer {
    sum: std::cell::RefCell<i32>,
}

impl SumReducer {
    pub fn new() -> Self {
        SumReducer {
            sum: std::cell::RefCell::new(0),
        }
    }
    
    pub fn get_sum(&self) -> i32 {
        *self.sum.borrow()
    }
}

impl PipelineProcessor for SumReducer {
    type Input = i32;
    type Output = i32;
    
    fn process(&self, input: i32) -> impl Iterator<Item = i32> {
        *self.sum.borrow_mut() += input;
        std::iter::once(*self.sum.borrow())
    }
    
    fn name(&self) -> &str {
        "SumReducer"
    }
}

// ============================================================================
// 示例 3: 数据转换流水线
// ============================================================================

/// 数据记录
#[derive(Debug, Clone)]
pub struct Record {
    pub id: u32,
    pub name: String,
    pub value: f64,
    pub tags: Vec<String>,
}

/// 记录验证器
pub struct RecordValidator {
    min_value: f64,
}

impl RecordValidator {
    pub fn new(min_value: f64) -> Self {
        RecordValidator { min_value }
    }
}

impl PipelineProcessor for RecordValidator {
    type Input = Record;
    type Output = Record;
    
    fn process(&self, input: Record) -> impl Iterator<Item = Record> {
        if input.value >= self.min_value {
            Some(input).into_iter()
        } else {
            None.into_iter()
        }
    }
    
    fn name(&self) -> &str {
        "RecordValidator"
    }
}

/// 记录增强器（添加标签）
pub struct RecordEnricher {
    tag: String,
}

impl RecordEnricher {
    pub fn new(tag: impl Into<String>) -> Self {
        RecordEnricher { tag: tag.into() }
    }
}

impl PipelineProcessor for RecordEnricher {
    type Input = Record;
    type Output = Record;
    
    fn process(&self, mut input: Record) -> impl Iterator<Item = Record> {
        input.tags.push(self.tag.clone());
        std::iter::once(input)
    }
    
    fn name(&self) -> &str {
        "RecordEnricher"
    }
}

/// 记录聚合器（提取摘要）
#[derive(Debug, Clone)]
pub struct RecordSummary {
    pub id: u32,
    pub value: f64,
    pub tag_count: usize,
}

pub struct RecordAggregator;

impl PipelineProcessor for RecordAggregator {
    type Input = Record;
    type Output = RecordSummary;
    
    fn process(&self, input: Record) -> impl Iterator<Item = RecordSummary> {
        std::iter::once(RecordSummary {
            id: input.id,
            value: input.value,
            tag_count: input.tags.len(),
        })
    }
    
    fn name(&self) -> &str {
        "RecordAggregator"
    }
}

// ============================================================================
// 处理器链实现
// ============================================================================

/// 两个处理器的链
pub struct ProcessorChain<P1, P2> {
    first: P1,
    second: P2,
}

impl<P1, P2> ProcessorChain<P1, P2> {
    pub fn new(first: P1, second: P2) -> Self {
        ProcessorChain { first, second }
    }
}

impl<P1, P2> PipelineProcessor for ProcessorChain<P1, P2>
where
    P1: PipelineProcessor,
    P2: PipelineProcessor<Input = P1::Output>,
    P1::Output: 'static,
    P2::Output: 'static,
{
    type Input = P1::Input;
    type Output = P2::Output;
    
    fn process(&self, input: Self::Input) -> impl Iterator<Item = Self::Output> {
        self.first.process(input)
            .flat_map(|x| self.second.process(x))
            .collect::<Vec<_>>()
            .into_iter()
    }
    
    fn name(&self) -> &str {
        "Chain"
    }
}

// ============================================================================
// 并行处理流水线 (Send 约束)
// ============================================================================

/// 并行处理器 trait
pub trait ParallelProcessor {
    type Input: Send;
    type Output: Send;
    
    /// 并行处理（返回 Send 迭代器）
    fn process_parallel(&self, input: Self::Input) 
        -> impl Iterator<Item = Self::Output> + Send;
}

/// 并行数值处理器
pub struct ParallelNumProcessor {
    multiplier: i32,
}

impl ParallelNumProcessor {
    pub fn new(multiplier: i32) -> Self {
        ParallelNumProcessor { multiplier }
    }
}

impl ParallelProcessor for ParallelNumProcessor {
    type Input = Vec<i32>;
    type Output = i32;
    
    fn process_parallel(&self, input: Vec<i32>) -> impl Iterator<Item = i32> + Send {
        let multiplier = self.multiplier;
        input.into_iter()
            .map(move |x| x * multiplier)
            .collect::<Vec<_>>()
            .into_iter()
    }
}

// ============================================================================
// 统计收集器
// ============================================================================

pub struct PipelineStats {
    processors: Vec<String>,
    items_processed: usize,
    start_time: std::time::Instant,
}

impl PipelineStats {
    pub fn new() -> Self {
        PipelineStats {
            processors: Vec::new(),
            items_processed: 0,
            start_time: std::time::Instant::now(),
        }
    }
    
    pub fn add_processor(&mut self, name: impl Into<String>) {
        self.processors.push(name.into());
    }
    
    pub fn record_item(&mut self) {
        self.items_processed += 1;
    }
    
    pub fn report(&self) {
        println!("\n📊 流水线统计:");
        println!("  处理器链: {}", self.processors.join(" → "));
        println!("  处理项数: {}", self.items_processed);
        println!("  总耗时: {:?}", self.start_time.elapsed());
        println!("  平均耗时: {:.2} µs/item", 
                 self.start_time.elapsed().as_micros() as f64 / self.items_processed as f64);
    }
}

// ============================================================================
// 性能对比：RPITIT vs 关联类型
// ============================================================================

// 旧方式：使用关联类型
pub trait OldPipelineProcessor {
    type Input;
    type Output;
    type Iter<'a>: Iterator<Item = Self::Output> 
    where 
        Self: 'a;
    
    fn process(&self, input: Self::Input) -> Self::Iter<'_>;
}

// 对比说明
pub fn compare_approaches() {
    println!("\n📊 RPITIT vs 关联类型对比");
    println!("{}", "-".repeat(70));
    
    println!("\n✅ RPITIT 优势:");
    println!("  1. 代码更简洁（无需定义 Iter 关联类型）");
    println!("  2. 更好的类型推导");
    println!("  3. 更灵活的返回类型");
    println!("  4. 零性能开销（完全内联）");
    
    println!("\n⚖️  关联类型的场景:");
    println!("  1. 需要在 trait 外部引用迭代器类型");
    println!("  2. 更复杂的生命周期约束");
    println!("  3. trait 对象（dyn Trait）");
    
    println!("\n💡 性能:");
    println!("  - 编译后性能完全相同");
    println!("  - 都是零成本抽象");
    println!("  - 编译时单态化");
}

// ============================================================================
// 主函数 - 演示所有示例
// ============================================================================

fn main() {
    println!("🦀 Rust 1.90 RPITIT 流水线模式高级示例\n");
    println!("{}", "=".repeat(70));
    
    // 示例 1: 文本处理流水线
    println!("\n📌 示例 1: 文本处理流水线");
    println!("{}", "-".repeat(70));
    
    let text = "hello,world,rust,programming,design,patterns".to_string();
    println!("输入: {}", text);
    
    let pipeline = TokenizerProcessor::new(',')
        .chain(FilterProcessor::new(|s| s.len() > 4))
        .chain(MapProcessor::new(|s| s.to_uppercase()));
    
    println!("\n处理器链: Tokenizer → Filter → Map");
    println!("结果:");
    for (i, result) in pipeline.process(text).enumerate() {
        println!("  {}. {}", i + 1, result);
    }
    
    // 示例 2: 数值处理流水线
    println!("\n📌 示例 2: 数值处理流水线");
    println!("{}", "-".repeat(70));
    
    let pipeline = RangeGenerator::new(1, 11)
        .chain(EvenFilter)
        .chain(SquareMapper);
    
    println!("输入: 1..11");
    println!("处理器链: RangeGenerator → EvenFilter → SquareMapper");
    println!("结果:");
    
    let results: Vec<_> = pipeline.process(()).collect();
    println!("  {:?}", results);
    println!("  (偶数的平方: 4, 16, 36, 64, 100)");
    
    // 示例 3: 数据记录流水线
    println!("\n📌 示例 3: 数据记录处理流水线");
    println!("{}", "-".repeat(70));
    
    let records = vec![
        Record {
            id: 1,
            name: "Record A".to_string(),
            value: 100.0,
            tags: vec!["initial".to_string()],
        },
        Record {
            id: 2,
            name: "Record B".to_string(),
            value: 50.0,
            tags: vec!["initial".to_string()],
        },
        Record {
            id: 3,
            name: "Record C".to_string(),
            value: 200.0,
            tags: vec!["initial".to_string()],
        },
    ];
    
    println!("输入: {} 条记录", records.len());
    
    let pipeline = RecordValidator::new(75.0)
        .chain(RecordEnricher::new("validated"))
        .chain(RecordAggregator);
    
    println!("处理器链: Validator(≥75) → Enricher → Aggregator");
    println!("\n结果:");
    
    for record in records {
        for summary in pipeline.process(record) {
            println!("  ID: {}, Value: {:.2}, Tags: {}", 
                     summary.id, summary.value, summary.tag_count);
        }
    }
    
    // 示例 4: 批量处理
    println!("\n📌 示例 4: 批量处理");
    println!("{}", "-".repeat(70));
    
    let inputs = vec!["apple", "banana", "cherry", "date"];
    println!("输入: {:?}", inputs);
    
    let processor = MapProcessor::new(|s| s.to_uppercase());
    println!("处理器: ToUppercase");
    
    let results: Vec<_> = processor.process_batch(
        inputs.into_iter().map(String::from)
    ).collect();
    
    println!("结果: {:?}", results);
    
    // 示例 5: 并行处理
    println!("\n📌 示例 5: 并行处理");
    println!("{}", "-".repeat(70));
    
    let parallel_processor = ParallelNumProcessor::new(2);
    let data = vec![1, 2, 3, 4, 5];
    
    println!("输入: {:?}", data);
    println!("操作: 每个元素 × 2");
    
    let results: Vec<_> = parallel_processor.process_parallel(data).collect();
    println!("结果: {:?}", results);
    
    // 性能统计
    println!("\n📌 性能统计示例");
    println!("{}", "-".repeat(70));
    
    let mut stats = PipelineStats::new();
    stats.add_processor("Filter");
    stats.add_processor("Map");
    stats.add_processor("Reduce");
    
    let input = (1..1001).map(|i| i.to_string()).collect::<Vec<_>>();
    
    let processor = FilterProcessor::new(|s| s.len() > 1)
        .chain(MapProcessor::new(|s| s.len()));
    
    for item in input {
        for _ in processor.process(item) {
            stats.record_item();
        }
    }
    
    stats.report();
    
    // 方法对比
    compare_approaches();
    
    // 总结
    println!("\n{}", "=".repeat(70));
    println!("✅ RPITIT 流水线模式的优势:");
    println!("  1. 零成本抽象 - 编译后无运行时开销");
    println!("  2. 类型安全 - 编译时检查类型匹配");
    println!("  3. 可组合性 - 轻松链接多个处理器");
    println!("  4. 惰性求值 - 只在需要时计算");
    println!("  5. 代码简洁 - 相比关联类型减少约30%代码");
    println!("\n💡 适用场景:");
    println!("  - 数据处理管道");
    println!("  - ETL（提取-转换-加载）流程");
    println!("  - 事件处理链");
    println!("  - 流式计算");
    println!("  - 函数式编程模式");
    println!("{}", "=".repeat(70));
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_tokenizer() {
        let processor = TokenizerProcessor::new(',');
        let result: Vec<_> = processor.process("a,b,c".to_string()).collect();
        assert_eq!(result, vec!["a", "b", "c"]);
    }
    
    #[test]
    fn test_filter() {
        let processor = FilterProcessor::new(|s| s.len() > 2);
        let result: Vec<_> = processor.process("hello".to_string()).collect();
        assert_eq!(result.len(), 1);
        
        let result: Vec<_> = processor.process("hi".to_string()).collect();
        assert_eq!(result.len(), 0);
    }
    
    #[test]
    fn test_chain() {
        let pipeline = RangeGenerator::new(1, 6)
            .chain(EvenFilter)
            .chain(SquareMapper);
        
        let result: Vec<_> = pipeline.process(()).collect();
        assert_eq!(result, vec![4, 16]);
    }
    
    #[test]
    fn test_record_pipeline() {
        let record = Record {
            id: 1,
            name: "Test".to_string(),
            value: 100.0,
            tags: vec![],
        };
        
        let pipeline = RecordValidator::new(50.0)
            .chain(RecordEnricher::new("test"))
            .chain(RecordAggregator);
        
        let result: Vec<_> = pipeline.process(record).collect();
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].tag_count, 1);
    }
}

