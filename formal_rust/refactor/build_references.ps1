# 建立文档间引用和链接的脚本
# 为所有目录的README文件添加相互引用

Write-Host "开始建立文档间引用..." -ForegroundColor Green

# 定义主要目录及其主题
$mainDirectories = @{
    "01_foundational_theory" = "理论基础"
    "02_programming_paradigms" = "编程范式"
    "03_design_patterns" = "设计模式"
    "04_industry_applications" = "行业应用"
    "05_concurrent_patterns" = "并发模式"
    "06_distributed_patterns" = "分布式模式"
    "07_workflow_patterns" = "工作流模式"
    "08_rust_language_theory" = "Rust语言理论"
    "09_async_programming" = "异步编程"
    "10_system_integration" = "系统集成"
    "11_performance_optimization" = "性能优化"
    "12_advanced_patterns" = "高级模式"
}

# 为每个目录创建标准化的README引用部分
foreach ($dir in $mainDirectories.Keys) {
    $readmePath = Join-Path $dir "00_readme.md"
    
    if (Test-Path $readmePath) {
        Write-Host "处理目录: $dir" -ForegroundColor Yellow
        
        # 读取现有内容
        $content = Get-Content $readmePath -Raw
        
        # 添加文档间引用部分
        $referenceSection = @"

## 相关文档引用

### 理论基础关联
- [01. 理论基础](../01_foundational_theory/00_readme.md) - 哲学和数学基础
- [02. 编程范式](../02_programming_paradigms/00_readme.md) - 编程理论体系
- [08. Rust语言理论](../08_rust_language_theory/00_readme.md) - Rust核心理论

### 设计模式关联
- [03. 设计模式](../03_design_patterns/00_readme.md) - 经典和高级设计模式
- [12. 高级模式](../12_advanced_patterns/00_readme.md) - 高级编程模式

### 工程实践关联
- [05. 并发模式](../05_concurrent_patterns/00_readme.md) - 并发编程模式
- [06. 分布式模式](../06_distributed_patterns/00_readme.md) - 分布式系统模式
- [07. 工作流模式](../07_workflow_patterns/00_readme.md) - 工作流工程模式
- [09. 异步编程](../09_async_programming/00_readme.md) - 异步编程理论

### 系统集成关联
- [10. 系统集成](../10_system_integration/00_readme.md) - 系统集成理论
- [11. 性能优化](../11_performance_optimization/00_readme.md) - 性能优化技术

### 行业应用关联
- [04. 行业应用](../04_industry_applications/00_readme.md) - 各行业应用实践

## 知识图谱

```mermaid
graph TD
    A[理论基础] --> B[编程范式]
    A --> C[Rust语言理论]
    B --> D[设计模式]
    B --> E[高级模式]
    D --> F[并发模式]
    D --> G[分布式模式]
    D --> H[工作流模式]
    E --> I[异步编程]
    F --> J[系统集成]
    G --> J
    H --> J
    I --> J
    J --> K[性能优化]
    K --> L[行业应用]
```

"@
        
        # 如果内容中还没有引用部分，则添加
        if ($content -notmatch "## 相关文档引用") {
            $newContent = $content + $referenceSection
            Set-Content -Path $readmePath -Value $newContent -Encoding UTF8
            Write-Host "已添加引用部分到: $readmePath" -ForegroundColor Green
        } else {
            Write-Host "引用部分已存在: $readmePath" -ForegroundColor Blue
        }
    }
}

# 创建主索引文件
$masterIndexContent = @"
# Rust形式化理论体系 - 主索引

## 目录结构

### 1. 理论基础 (01_foundational_theory)
- [哲学基础](./01_foundational_theory/00_readme.md)
- [数学基础](./01_foundational_theory/00_readme.md)
- [类型理论](./01_foundational_theory/00_readme.md)

### 2. 编程范式 (02_programming_paradigms)
- [编程语言理论](./02_programming_paradigms/00_readme.md)
- [软件工程理论](./02_programming_paradigms/00_readme.md)

### 3. 设计模式 (03_design_patterns)
- [创建型模式](./03_design_patterns/00_readme.md)
- [结构型模式](./03_design_patterns/00_readme.md)
- [行为型模式](./03_design_patterns/00_readme.md)

### 4. 行业应用 (04_industry_applications)
- [游戏开发](./04_industry_applications/00_readme.md)
- [IoT系统](./04_industry_applications/00_readme.md)
- [AI/ML应用](./04_industry_applications/00_readme.md)
- [区块链](./04_industry_applications/00_readme.md)
- [网络安全](./04_industry_applications/00_readme.md)
- [医疗健康](./04_industry_applications/00_readme.md)

### 5. 并发模式 (05_concurrent_patterns)
- [并发编程模式](./05_concurrent_patterns/00_readme.md)
- [并行计算模式](./05_concurrent_patterns/00_readme.md)

### 6. 分布式模式 (06_distributed_patterns)
- [分布式系统理论](./06_distributed_patterns/00_readme.md)
- [分布式模式](./06_distributed_patterns/00_readme.md)

### 7. 工作流模式 (07_workflow_patterns)
- [工作流模式](./07_workflow_patterns/00_readme.md)
- [工作流工程](./07_workflow_patterns/00_readme.md)

### 8. Rust语言理论 (08_rust_language_theory)
- [Rust核心理论](./08_rust_language_theory/00_readme.md)
- [类型系统](./08_rust_language_theory/00_readme.md)
- [内存模型](./08_rust_language_theory/00_readme.md)

### 9. 异步编程 (09_async_programming)
- [异步编程理论](./09_async_programming/00_readme.md)
- [Future/Promise模式](./09_async_programming/00_readme.md)

### 10. 系统集成 (10_system_integration)
- [系统集成理论](./10_system_integration/00_readme.md)
- [架构集成](./10_system_integration/00_readme.md)

### 11. 性能优化 (11_performance_optimization)
- [性能优化技术](./11_performance_optimization/00_readme.md)
- [性能分析](./11_performance_optimization/00_readme.md)

### 12. 高级模式 (12_advanced_patterns)
- [高级编程模式](./12_advanced_patterns/00_readme.md)
- [元编程](./12_advanced_patterns/00_readme.md)

## 知识体系图谱

```mermaid
graph TB
    subgraph "理论基础层"
        A1[哲学基础]
        A2[数学基础]
        A3[类型理论]
    end
    
    subgraph "编程理论层"
        B1[编程范式]
        B2[Rust语言理论]
    end
    
    subgraph "设计模式层"
        C1[设计模式]
        C2[高级模式]
    end
    
    subgraph "工程实践层"
        D1[并发模式]
        D2[分布式模式]
        D3[工作流模式]
        D4[异步编程]
    end
    
    subgraph "系统集成层"
        E1[系统集成]
        E2[性能优化]
    end
    
    subgraph "应用实践层"
        F1[行业应用]
    end
    
    A1 --> B1
    A2 --> B1
    A3 --> B2
    B1 --> C1
    B2 --> C2
    C1 --> D1
    C1 --> D2
    C1 --> D3
    C2 --> D4
    D1 --> E1
    D2 --> E1
    D3 --> E1
    D4 --> E1
    E1 --> E2
    E2 --> F1
```

## 快速导航

### 按主题分类
- **理论**: [01](./01_foundational_theory/00_readme.md) | [02](./02_programming_paradigms/00_readme.md) | [08](./08_rust_language_theory/00_readme.md)
- **设计**: [03](./03_design_patterns/00_readme.md) | [12](./12_advanced_patterns/00_readme.md)
- **工程**: [05](./05_concurrent_patterns/00_readme.md) | [06](./06_distributed_patterns/00_readme.md) | [07](./07_workflow_patterns/00_readme.md) | [09](./09_async_programming/00_readme.md)
- **系统**: [10](./10_system_integration/00_readme.md) | [11](./11_performance_optimization/00_readme.md)
- **应用**: [04](./04_industry_applications/00_readme.md)

### 按复杂度分类
- **基础**: 01, 02, 03
- **中级**: 05, 06, 07, 08, 09
- **高级**: 10, 11, 12
- **应用**: 04

## 更新日志

- **2024-12-19**: 完成目录重构和文件命名规范化
- **2024-12-19**: 建立文档间引用和链接系统
- **2024-12-19**: 创建主索引和知识图谱

"@

Set-Content -Path "master_index.md" -Value $masterIndexContent -Encoding UTF8
Write-Host "已创建主索引文件: master_index.md" -ForegroundColor Green

Write-Host "文档间引用建立完成!" -ForegroundColor Green 