# 🔍 Rust Documentation Intelligent Search Tool

> **Version**: v1.1  
> **Created**: 2025-10-20  
> **Updated**: 2025-10-20  
> **Status**: ✅ Fully Implemented (v1.1 Features)

---

## 📋 Table of Contents

- [Introduction](#introduction)
- [Features](#features)
- [Installation](#installation)
- [Usage](#usage)
- [Configuration](#configuration)
- [Examples](#examples)
- [Performance](#performance)

---

## Introduction

The **Rust Documentation Intelligent Search Tool** is a powerful documentation search system designed for the Rust learning project. It can quickly index and search all documentation in the project, with multi-dimensional filtering and intelligent ranking.

### Core Advantages

- ⚡ **Fast Indexing** - Auto-build document index with incremental updates
- 🎯 **Precise Search** - Intelligent ranking based on relevance scores
- 🔍 **Multi-dimensional Filtering** - Filter by module and document type
- 📊 **Statistical Analysis** - Detailed documentation statistics
- 🎨 **User-friendly Interface** - Colored output with clear results
- 🔬 **Advanced Features** - Regex search, fuzzy search, result export

---

## Features

### 1. Full-text Search

- Chinese and English keyword search
- Intelligent word segmentation and relevance scoring
- Context preview
- Command-line highlighting
- **New**: Regular expression search
- **New**: Fuzzy search

### 2. Multi-dimensional Filtering

**Filter by Module**:

```bash
rust-doc-search search "ownership" --module c01_ownership_borrow_scope
```

**Filter by Document Type**:

```bash
rust-doc-search search "async" --doc-type examples
```

### 3. Advanced Search (v1.1 New)

**Regular Expression Search**:

```bash
rust-doc-search search "\b(async|await)\b" --regex
```

**Fuzzy Search**:

```bash
rust-doc-search search "ownershp" --fuzzy  # Can find "ownership"
```

**Export Search Results**:

```bash
# Export as JSON
rust-doc-search search "concurrency" -o results.json

# Export as CSV
rust-doc-search search "trait" -o results.csv -F csv

# Export as Markdown
rust-doc-search search "async" -o results.md -F markdown
```

### 4. Configuration Management (v1.1 New)

**Generate Configuration File**:

```bash
rust-doc-search init-config
```

**Custom Configuration**:

```toml
# ~/.config/rust-doc-search/config.toml
default_max_results = 20
default_min_score = 1.0
incremental_index = true
enable_history = true

[advanced]
enable_regex = true
enable_fuzzy = true
fuzzy_threshold = 0.7
context_lines = 2
```

### 5. Cache Management (v1.1 New)

```bash
# Clear cache (force rebuild index)
rust-doc-search clear-cache
```

### 6. Document Types Supported

| Icon | Type | Description |
|------|------|-------------|
| 📊 | `KnowledgeGraph` | Knowledge graph documents |
| 📐 | `ComparisonMatrix` | Multi-dimensional comparison matrices |
| 🗺️ | `MindMap` | Mind maps |
| 💻 | `Examples` | Practical examples |
| 📋 | `Report` | Enhancement reports |
| 📘 | `MainDoc` | Main documents |
| 🎓 | `Theory` | Theoretical documents |

---

## Installation

### Prerequisites

- Rust 1.90+ (recommended to use latest stable version)
- Cargo

### Build

```bash
cd tools/doc_search
cargo build --release
```

### Install to System

```bash
cargo install --path .
```

---

## Usage

### Basic Search

```bash
# Search keyword
rust-doc-search search "ownership"

# Search multiple keywords
rust-doc-search search "ownership borrow"
```

### Advanced Search

```bash
# Search in specific module
rust-doc-search search "async" --module c06_async

# Search in specific document type
rust-doc-search search "trait" --doc-type theory

# Set maximum results
rust-doc-search search "Rust" --max-results 10

# Set minimum score threshold
rust-doc-search search "concurrency" --min-score 2.0

# Use regex search
rust-doc-search search "\bstruct\b" --regex

# Use fuzzy search
rust-doc-search search "asyncronous" --fuzzy

# Export results
rust-doc-search search "lifetime" -o output.json -F json
```

### Browse Documentation

```bash
# View statistics
rust-doc-search stats

# List all modules
rust-doc-search modules

# View all documents in a specific module
rust-doc-search module c05_threads

# View all documents containing a specific keyword
rust-doc-search keyword "generic"
```

---

## Configuration

### Generate Default Configuration

```bash
rust-doc-search init-config
```

This creates a configuration file at `~/.config/rust-doc-search/config.toml` with default settings.

### Configuration Options

```toml
# Project root directory
root_path = "/path/to/rust-lang"

# Default maximum search results
default_max_results = 20

# Default minimum relevance score
default_min_score = 1.0

# Index cache path
cache_path = "~/.cache/rust-doc-search/index.cache"

# Enable incremental indexing
incremental_index = true

# Enable search history
enable_history = true

# Maximum history records
max_history = 100

# Export format (json, csv, markdown)
export_format = "json"

[advanced]
# Enable regular expression search
enable_regex = true

# Enable fuzzy search
enable_fuzzy = true

# Fuzzy search threshold (0.0-1.0)
fuzzy_threshold = 0.7

# Context lines
context_lines = 2
```

---

## Examples

### Example 1: Search Ownership-related Documents

```bash
$ rust-doc-search search "ownership"

🔍 Searching: 'ownership'

✅ Found 15 results
────────────────────────────────────────────────────────────────────────────────

1. 📊 crates/c01_ownership_borrow_scope/docs/theory/KNOWLEDGE_GRAPH.md:42
   Module: c01_ownership_borrow_scope | Type: KnowledgeGraph | Score: 5.5
   ## Ownership Core Concepts

2. 📐 crates/c01_ownership_borrow_scope/docs/theory/MULTI_DIMENSIONAL_MATRIX.md:78
   Module: c01_ownership_borrow_scope | Type: ComparisonMatrix | Score: 4.0
   | **Ownership Transfer** | Move semantics | ...

...
```

### Example 2: Search in Async Module

```bash
$ rust-doc-search search "Future" --module c06_async --max-results 5

🔍 Searching: 'Future'
   Module filter: c06_async

✅ Found 5 results
────────────────────────────────────────────────────────────────────────────────

1. 💻 crates/c06_async/docs/RUST_190_EXAMPLES.md:120
   Module: c06_async | Type: Examples | Score: 3.5
   impl Future for MyFuture { ... }

...
```

### Example 3: View Statistics

```bash
$ rust-doc-search stats

📊 Documentation Statistics
────────────────────────────────────────────────────────────────────────────────

📄 Total Documents: 35
📦 Total Modules: 14
🔑 Total Keywords: 127

📚 Document Type Distribution:
   📊 KnowledgeGraph: 13
   📐 ComparisonMatrix: 13
   🗺️ MindMap: 4
   💻 Examples: 6
   📋 Report: 13
   📘 MainDoc: 15
   🎓 Theory: 1
```

---

## Performance

| Metric | Value |
|--------|-------|
| **Index Build Time** | ~500ms (35 documents) |
| **Search Response Time** | <50ms |
| **Memory Usage** | ~10MB |
| **Supported Documents** | 1000+ |

---

## Development Roadmap

### v1.0 ✅ (Completed)

- [x] Basic search functionality
- [x] Multi-dimensional filtering
- [x] Statistics information
- [x] CLI interface
- [x] Colored output

### v1.1 ✅ (Current Version)

- [x] Incremental index updates
- [x] Configuration file support
- [x] Export search results (JSON/CSV/Markdown)
- [x] Regular expression search
- [x] Fuzzy search
- [x] Cache management

### v2.0 (Future)

- [ ] Web interface
- [ ] Semantic search
- [ ] AI-assisted search
- [ ] Search history
- [ ] Custom scoring algorithms

---

## License

MIT License

---

**Documentation Version**: v1.1  
**Last Updated**: 2025-10-20  
**Maintainer**: Rust Learning Community

---

🎉 **Start using the Rust Documentation Intelligent Search Tool to quickly find the knowledge you need!** 🔍✨
