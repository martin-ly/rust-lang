# 🛠️ Rust 文档工具链设计

> **文档创建**: 2025-10-20  
> **目标**: 提升文档可用性和学习效率  
> **技术栈**: Rust + mdBook + 自定义工具

---

## 📋 目录

- [🛠️ Rust 文档工具链设计](#️-rust-文档工具链设计)
  - [📋 目录](#-目录)
  - [🎯 工具链总览](#-工具链总览)
  - [📚 工具1: 文档导航生成器](#-工具1-文档导航生成器)
    - [核心功能](#核心功能)
    - [实现设计](#实现设计)
  - [🔍 工具2: 智能文档搜索](#-工具2-智能文档搜索)
    - [核心功能2](#核心功能2)
    - [实现设计2](#实现设计2)
  - [📊 工具3: 学习进度追踪](#-工具3-学习进度追踪)
    - [核心功能3](#核心功能3)
    - [实现设计3](#实现设计3)
  - [🧪 工具4: 代码示例验证器](#-工具4-代码示例验证器)
    - [核心功能4](#核心功能4)
    - [实现设计4](#实现设计4)
  - [📈 工具5: 性能基准套件](#-工具5-性能基准套件)
    - [核心功能5](#核心功能5)
    - [实现设计5](#实现设计5)
  - [🌐 工具6: 交互式文档网站](#-工具6-交互式文档网站)
    - [核心功能6](#核心功能6)
    - [技术栈](#技术栈)
  - [📁 工具链项目结构](#-工具链项目结构)
  - [✅ 实施计划](#-实施计划)
    - [Phase 1: 核心工具 (Week 1)](#phase-1-核心工具-week-1)
    - [Phase 2: 辅助工具 (Week 2)](#phase-2-辅助工具-week-2)
    - [Phase 3: 高级功能 (Week 3)](#phase-3-高级功能-week-3)
    - [Phase 4: 优化与推广 (持续)](#phase-4-优化与推广-持续)

---

## 🎯 工具链总览

| 工具 | 功能 | 优先级 | 技术栈 |
|------|------|--------|--------|
| 文档导航生成器 | 自动生成目录和索引 | ⭐⭐⭐⭐⭐ | Rust/walkdir |
| 智能文档搜索 | 全文搜索和语义搜索 | ⭐⭐⭐⭐⭐ | Rust/tantivy |
| 学习进度追踪 | 跟踪学习进度 | ⭐⭐⭐⭐ | Rust/serde |
| 代码示例验证 | 验证代码正确性 | ⭐⭐⭐⭐⭐ | Rust/cargo |
| 性能基准套件 | 性能测试框架 | ⭐⭐⭐ | Rust/criterion |
| 交互式网站 | Web文档浏览 | ⭐⭐⭐⭐⭐ | mdBook/JS |

---

## 📚 工具1: 文档导航生成器

### 核心功能

自动扫描项目文档，生成：

- 📖 总目录（MASTER_INDEX.md）
- 🗺️ 模块导航图
- 🔗 文档间链接验证
- 📊 文档统计报告

### 实现设计

```rust
// 文档扫描器
struct DocScanner {
    root_path: PathBuf,
    ignores: Vec<String>,
}

impl DocScanner {
    fn scan(&self) -> Result<DocTree> {
        // 递归扫描所有.md文件
        let entries = WalkDir::new(&self.root_path)
            .into_iter()
            .filter_entry(|e| !self.should_ignore(e))
            .collect();
        
        self.build_tree(entries)
    }
    
    fn generate_index(&self, tree: &DocTree) -> String {
        // 生成目录结构
        let mut output = String::new();
        output.push_str("# 📚 Rust 学习文档总目录\n\n");
        
        for module in &tree.modules {
            output.push_str(&format!("## {}\n\n", module.name));
            for doc in &module.docs {
                output.push_str(&format!("- [{}]({})\n", doc.title, doc.path));
            }
        }
        
        output
    }
}

// 链接验证器
struct LinkValidator {
    base_path: PathBuf,
}

impl LinkValidator {
    fn validate(&self, tree: &DocTree) -> Vec<BrokenLink> {
        let mut broken = Vec::new();
        
        for doc in tree.all_docs() {
            let links = self.extract_links(&doc);
            for link in links {
                if !self.link_exists(&link) {
                    broken.push(BrokenLink {
                        source: doc.path.clone(),
                        target: link,
                    });
                }
            }
        }
        
        broken
    }
}
```

**使用示例**:

```bash
# 生成总目录
$ rust-doc-nav generate --output MASTER_INDEX.md

# 验证链接
$ rust-doc-nav validate --fix

# 生成统计报告
$ rust-doc-nav stats
```

---

## 🔍 工具2: 智能文档搜索

### 核心功能2

- 🔎 全文搜索（关键词、正则）
- 🧠 语义搜索（相关文档）
- 📑 按模块/主题过滤
- ⚡ 实时增量索引

### 实现设计2

```rust
use tantivy::*;

// 搜索引擎
struct DocSearchEngine {
    index: Index,
    reader: IndexReader,
}

impl DocSearchEngine {
    fn new(docs_path: &Path) -> Result<Self> {
        let schema = Self::build_schema();
        let index = Index::create_in_dir(docs_path, schema)?;
        
        // 索引所有文档
        let mut writer = index.writer(50_000_000)?;
        Self::index_documents(&mut writer, docs_path)?;
        writer.commit()?;
        
        Ok(Self {
            index,
            reader: index.reader()?,
        })
    }
    
    fn search(&self, query: &str, limit: usize) -> Result<Vec<SearchResult>> {
        let searcher = self.reader.searcher();
        let query_parser = QueryParser::for_index(&self.index, vec![]);
        
        let query = query_parser.parse_query(query)?;
        let results = searcher.search(&query, &TopDocs::with_limit(limit))?;
        
        self.format_results(results, &searcher)
    }
    
    fn build_schema() -> Schema {
        let mut schema_builder = Schema::builder();
        schema_builder.add_text_field("title", TEXT | STORED);
        schema_builder.add_text_field("content", TEXT);
        schema_builder.add_text_field("module", STRING | STORED);
        schema_builder.add_text_field("path", STRING | STORED);
        schema_builder.build()
    }
}

// CLI接口
#[derive(Parser)]
struct SearchArgs {
    /// 搜索查询
    query: String,
    
    /// 限制结果数
    #[arg(short, long, default_value = "10")]
    limit: usize,
    
    /// 模块过滤
    #[arg(short, long)]
    module: Option<String>,
}
```

**使用示例**:

```bash
# 搜索关键词
$ rust-doc-search "async trait"

# 限制模块
$ rust-doc-search "ownership" --module c01

# 正则搜索
$ rust-doc-search --regex "C0[1-5].*"
```

---

## 📊 工具3: 学习进度追踪

### 核心功能3

- ✅ 标记已完成的章节
- 📈 可视化学习进度
- 🎯 推荐下一步学习内容
- 📅 学习时间统计

### 实现设计3

```rust
// 学习进度
#[derive(Serialize, Deserialize)]
struct LearningProgress {
    user: String,
    completed: HashSet<String>,
    started: HashMap<String, DateTime<Utc>>,
    notes: HashMap<String, String>,
}

impl LearningProgress {
    fn mark_complete(&mut self, doc_path: &str) {
        self.completed.insert(doc_path.to_string());
    }
    
    fn get_progress(&self, module: &str) -> f64 {
        let total = self.count_docs_in_module(module);
        let completed = self.completed
            .iter()
            .filter(|p| p.starts_with(module))
            .count();
        
        completed as f64 / total as f64 * 100.0
    }
    
    fn recommend_next(&self) -> Vec<String> {
        // 基于已完成的内容推荐下一步
        let mut candidates = Vec::new();
        
        // 规则: 完成C01后推荐C02
        if self.module_completed("c01") && !self.module_started("c02") {
            candidates.push("c02_type_system".to_string());
        }
        
        candidates
    }
}

// CLI接口
#[derive(Parser)]
enum ProgressCmd {
    /// 标记完成
    Complete { path: String },
    
    /// 查看进度
    Show { module: Option<String> },
    
    /// 获取推荐
    Recommend,
    
    /// 添加笔记
    Note { path: String, note: String },
}
```

**使用示例**:

```bash
# 标记完成
$ rust-doc-progress complete c01/docs/ownership.md

# 查看进度
$ rust-doc-progress show
$ rust-doc-progress show --module c05

# 获取推荐
$ rust-doc-progress recommend

# 添加笔记
$ rust-doc-progress note c02/types.md "重点理解Trait对象"
```

---

## 🧪 工具4: 代码示例验证器

### 核心功能4

- ✅ 提取所有代码块
- 🧪 自动编译验证
- 📊 生成测试报告
- 🔄 持续集成支持

### 实现设计4

```rust
// 代码提取器
struct CodeExtractor {
    md_parser: Parser<'static>,
}

impl CodeExtractor {
    fn extract_code_blocks(&self, md_content: &str) -> Vec<CodeBlock> {
        let mut blocks = Vec::new();
        
        for event in Parser::new(md_content) {
            if let Event::Code(code) = event {
                blocks.push(CodeBlock {
                    language: "rust".to_string(),
                    content: code.to_string(),
                    line_number: 0, // TODO: track line
                });
            }
        }
        
        blocks
    }
}

// 代码验证器
struct CodeValidator {
    temp_dir: TempDir,
}

impl CodeValidator {
    async fn validate(&self, block: &CodeBlock) -> ValidationResult {
        // 1. 创建临时项目
        let project = self.create_temp_project(&block)?;
        
        // 2. 运行cargo check
        let output = Command::new("cargo")
            .arg("check")
            .current_dir(&project)
            .output()
            .await?;
        
        // 3. 解析结果
        ValidationResult {
            success: output.status.success(),
            stdout: String::from_utf8_lossy(&output.stdout).to_string(),
            stderr: String::from_utf8_lossy(&output.stderr).to_string(),
        }
    }
    
    fn create_temp_project(&self, block: &CodeBlock) -> Result<PathBuf> {
        let project_dir = self.temp_dir.path().join("test_project");
        fs::create_dir_all(&project_dir)?;
        
        // 写入Cargo.toml
        let cargo_toml = format!(
            r#"
            [package]
            name = "test"
            version = "0.1.0"
            edition = "2024"
            
            [dependencies]
            tokio = {{ version = "1", features = ["full"] }}
            "#
        );
        fs::write(project_dir.join("Cargo.toml"), cargo_toml)?;
        
        // 写入代码
        let main_rs = project_dir.join("src/main.rs");
        fs::create_dir_all(main_rs.parent().unwrap())?;
        fs::write(main_rs, &block.content)?;
        
        Ok(project_dir)
    }
}
```

**使用示例**:

```bash
# 验证所有代码示例
$ rust-doc-validate --all

# 验证特定模块
$ rust-doc-validate --module c06

# 生成报告
$ rust-doc-validate --report validation-report.html
```

---

## 📈 工具5: 性能基准套件

### 核心功能5

- ⚡ 标准化性能测试
- 📊 结果可视化对比
- 📈 历史趋势分析
- 🔧 CI/CD集成

### 实现设计5

```rust
use criterion::{criterion_group, criterion_main, Criterion};

// 基准测试配置
struct BenchmarkSuite {
    modules: Vec<ModuleBenchmark>,
}

struct ModuleBenchmark {
    name: String,
    benchmarks: Vec<Box<dyn Fn(&mut Criterion)>>,
}

// 示例: C08 算法模块基准测试
fn c08_benchmarks(c: &mut Criterion) {
    c.bench_function("quick_sort_10k", |b| {
        let data: Vec<i32> = (0..10_000).collect();
        b.iter(|| quick_sort(&data))
    });
    
    c.bench_function("merge_sort_10k", |b| {
        let data: Vec<i32> = (0..10_000).collect();
        b.iter(|| merge_sort(&data))
    });
}

criterion_group!(benches, c08_benchmarks);
criterion_main!(benches);
```

**使用示例**:

```bash
# 运行所有基准测试
$ cargo bench --all

# 运行特定模块
$ cargo bench --package c08_algorithms

# 生成HTML报告
$ cargo bench -- --save-baseline main
```

---

## 🌐 工具6: 交互式文档网站

### 核心功能6

- 📖 美观的文档浏览
- 🔍 集成搜索功能
- 🎨 代码高亮和复制
- 📱 响应式设计

### 技术栈

- **mdBook**: 静态网站生成
- **highlight.js**: 代码高亮
- **lunr.js**: 客户端搜索
- **自定义主题**: Rust风格

**mdBook配置**:

```toml
# book.toml
[book]
title = "Rust 1.90 学习指南"
authors = ["Rust Learning Community"]
language = "zh-CN"

[output.html]
default-theme = "rust"
git-repository-url = "https://github.com/..."
edit-url-template = "https://github.com/.../edit/main/{path}"

[output.html.search]
enable = true
limit-results = 30

[output.html.playground]
runnable = true
```

**部署脚本**:

```bash
#!/bin/bash
# deploy.sh

echo "构建文档网站..."
mdbook build

echo "部署到GitHub Pages..."
cd book
git init
git add .
git commit -m "Deploy documentation"
git push -f git@github.com:user/repo.git master:gh-pages
```

---

## 📁 工具链项目结构

```text
rust-doc-toolchain/
├── doc-navigator/          # 工具1: 导航生成器
│   ├── src/
│   └── Cargo.toml
├── doc-search/             # 工具2: 智能搜索
│   ├── src/
│   └── Cargo.toml
├── doc-progress/           # 工具3: 进度追踪
│   ├── src/
│   └── Cargo.toml
├── doc-validator/          # 工具4: 代码验证
│   ├── src/
│   └── Cargo.toml
├── doc-benchmark/          # 工具5: 性能基准
│   ├── benches/
│   └── Cargo.toml
├── doc-website/            # 工具6: 交互式网站
│   ├── book.toml
│   ├── src/
│   └── theme/
└── Cargo.workspace
```

---

## ✅ 实施计划

### Phase 1: 核心工具 (Week 1)

- [ ] 实现文档导航生成器
- [ ] 实现智能文档搜索
- [ ] 生成第一版总目录

### Phase 2: 辅助工具 (Week 2)

- [ ] 实现学习进度追踪
- [ ] 实现代码示例验证器
- [ ] 集成到CI/CD

### Phase 3: 高级功能 (Week 3)

- [ ] 实现性能基准套件
- [ ] 构建交互式文档网站
- [ ] 部署到GitHub Pages

### Phase 4: 优化与推广 (持续)

- [ ] 性能优化
- [ ] 用户体验改进
- [ ] 社区反馈收集

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20  
**维护者**: Rust Learning Community

---

*好的工具事半功倍！让我们构建更好的学习体验！* 🛠️✨
