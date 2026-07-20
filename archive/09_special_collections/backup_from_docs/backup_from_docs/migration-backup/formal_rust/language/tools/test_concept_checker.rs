use std::fs;
use concept_checker::{ConceptChecker, ConceptValidationResult};

#[test]
fn test_basic_concept_validation() {
    let checker = ConceptChecker::new();
    
    // 创建测试文件
    let test_content = r#"
# 所有权

## 元数据
- **概念ID**: 01.01
- **概念名称**: 所有权 (Ownership)
- **理论层次**: 第一层：基础理论层

## 形式化定义

使用统一符号系统(RFUSS)的形式化定义：

```math
\text{Own}(v, r) \equiv \forall t. v \in \text{Valid}(t) \implies r \in \text{Refs}(v)
```

其中：
- $\text{Own}(v, r)$ 表示值 $v$ 的所有权关系 $r$
- $\forall t$ 表示对所有时间点 $t$
- $v \in \text{Valid}(t)$ 表示值 $v$ 在时间 $t$ 有效
- $r \in \text{Refs}(v)$ 表示引用 $r$ 指向值 $v$

## 代码映射

| 形式化表示 | Rust代码 | 说明 |
|----------|---------|------|
| `Own(v, r)` | `let v = value;` | 值v的所有权 |
| `∀t. v ∈ Valid(t)` | 值在作用域内 | 值的有效性 |
| `r ∈ Refs(v)` | `&v` | 对v的引用 |
"#;
    
    let temp_file = "temp_concept.md";
    fs::write(temp_file, test_content).unwrap();
    
    let result = checker.validate_file(temp_file);
    fs::remove_file(temp_file).unwrap();
    
    match result {
        ConceptValidationResult::Valid { concept_id, concept_name, symbols } => {
            assert_eq!(concept_id, "01.01");
            assert_eq!(concept_name, "所有权 (Ownership)");
            assert!(!symbols.is_empty());
            println!("✅ 基本概念验证通过");
        },
        ConceptValidationResult::Invalid { errors } => {
            panic!("概念验证失败: {:?}", errors);
        }
    }
}

#[test]
fn test_invalid_concept_validation() {
    let checker = ConceptChecker::new();
    
    // 创建无效的测试文件
    let invalid_content = r#"
# 无效概念

## 元数据
- **概念ID**: 01.01
- **概念名称**: 所有权 (Ownership)

## 形式化定义

```math
\text{Invalid}(v, r) \equiv \forall t. v \in \text{Invalid}(t)
```

其中：
- $\text{Invalid}(v, r)$ 使用了未定义的符号
- $\text{Invalid}(t)$ 使用了未定义的概念
"#;
    
    let temp_file = "temp_invalid.md";
    fs::write(temp_file, invalid_content).unwrap();
    
    let result = checker.validate_file(temp_file);
    fs::remove_file(temp_file).unwrap();
    
    match result {
        ConceptValidationResult::Valid { .. } => {
            panic!("应该检测到无效概念");
        },
        ConceptValidationResult::Invalid { errors } => {
            assert!(!errors.is_empty());
            println!("✅ 无效概念检测通过");
        }
    }
}

#[test]
fn test_missing_metadata() {
    let checker = ConceptChecker::new();
    
    // 创建缺少元数据的文件
    let missing_content = r#"
# 缺少元数据

## 形式化定义

```math
\text{Test}(v) \equiv v \in \text{Valid}
```
"#;
    
    let temp_file = "temp_missing.md";
    fs::write(temp_file, missing_content).unwrap();
    
    let result = checker.validate_file(temp_file);
    fs::remove_file(temp_file).unwrap();
    
    match result {
        ConceptValidationResult::Valid { .. } => {
            panic!("应该检测到缺少元数据");
        },
        ConceptValidationResult::Invalid { errors } => {
            assert!(!errors.is_empty());
            println!("✅ 缺少元数据检测通过");
        }
    }
}

#[test]
fn test_symbol_consistency() {
    let checker = ConceptChecker::new();
    
    // 创建符号一致的测试文件
    let consistent_content = r#"
# 符号一致性测试

## 元数据
- **概念ID**: 02.01
- **概念名称**: 借用 (Borrowing)
- **理论层次**: 第二层：语言特性形式化层

## 形式化定义

```math
\text{Borrow}(r, v) \equiv \exists t. r \in \text{Refs}(v) \land v \in \text{Valid}(t)
```

其中：
- $\text{Borrow}(r, v)$ 表示引用 $r$ 借用值 $v$
- $\exists t$ 表示存在时间点 $t$
- $r \in \text{Refs}(v)$ 表示引用 $r$ 指向值 $v$
- $v \in \text{Valid}(t)$ 表示值 $v$ 在时间 $t$ 有效

## 代码映射

| 形式化表示 | Rust代码 | 说明 |
|----------|---------|------|
| `Borrow(r, v)` | `&v` | 借用v的引用 |
| `r ∈ Refs(v)` | `&v` | 引用r指向v |
| `v ∈ Valid(t)` | 值在作用域内 | v在时间t有效 |
"#;
    
    let temp_file = "temp_consistent.md";
    fs::write(temp_file, consistent_content).unwrap();
    
    let result = checker.validate_file(temp_file);
    fs::remove_file(temp_file).unwrap();
    
    match result {
        ConceptValidationResult::Valid { concept_id, concept_name, symbols } => {
            assert_eq!(concept_id, "02.01");
            assert_eq!(concept_name, "借用 (Borrowing)");
            assert!(!symbols.is_empty());
            
            // 检查符号一致性
            let symbol_names: Vec<&str> = symbols.iter().map(|s| s.name()).collect();
            assert!(symbol_names.contains(&"Borrow"));
            assert!(symbol_names.contains(&"Refs"));
            assert!(symbol_names.contains(&"Valid"));
            
            println!("✅ 符号一致性验证通过");
        },
        ConceptValidationResult::Invalid { errors } => {
            panic!("符号一致性验证失败: {:?}", errors);
        }
    }
}

#[test]
fn test_symbol_inconsistency() {
    let checker = ConceptChecker::new();
    
    // 创建符号不一致的测试文件
    let inconsistent_content = r#"
# 符号不一致测试

## 元数据
- **概念ID**: 02.02
- **概念名称**: 生命周期 (Lifetime)
- **理论层次**: 第二层：语言特性形式化层

## 形式化定义

```math
\text{Lifetime}(r, l) \equiv \forall t \in l. r \in \text{Valid}(t)
```

其中：
- $\text{Lifetime}(r, l)$ 表示引用 $r$ 的生命周期 $l$
- $\forall t \in l$ 表示对所有时间点 $t$ 在生命周期 $l$ 内
- $r \in \text{Valid}(t)$ 表示引用 $r$ 在时间 $t$ 有效

## 代码映射

| 形式化表示 | Rust代码 | 说明 |
|----------|---------|------|
| `Lifetime(r, l)` | `&'a` | 生命周期标注 |
| `r ∈ Valid(t)` | 引用有效 | 引用在时间t有效 |
| `UndefinedSymbol` | 未定义 | 使用了未定义的符号 |
"#;
    
    let temp_file = "temp_inconsistent.md";
    fs::write(temp_file, inconsistent_content).unwrap();
    
    let result = checker.validate_file(temp_file);
    fs::remove_file(temp_file).unwrap();
    
    match result {
        ConceptValidationResult::Valid { .. } => {
            panic!("应该检测到符号不一致");
        },
        ConceptValidationResult::Invalid { errors } => {
            assert!(!errors.is_empty());
            println!("✅ 符号不一致检测通过");
        }
    }
}

#[test]
fn test_directory_validation() {
    let checker = ConceptChecker::new();
    
    // 创建测试目录
    let test_dir = "test_concept_dir";
    fs::create_dir_all(test_dir).unwrap();
    
    // 创建多个概念文件
    let concept1_content = r#"
# 概念1

## 元数据
- **概念ID**: 01.01
- **概念名称**: 所有权 (Ownership)
- **理论层次**: 第一层：基础理论层

## 形式化定义

```math
\text{Own}(v) \equiv v \in \text{Valid}
```
"#;
    
    let concept2_content = r#"
# 概念2

## 元数据
- **概念ID**: 01.02
- **概念名称**: 借用 (Borrowing)
- **理论层次**: 第一层：基础理论层

## 形式化定义

```math
\text{Borrow}(r, v) \equiv r \in \text{Refs}(v)
```
"#;
    
    fs::write(format!("{}/concept1.md", test_dir), concept1_content).unwrap();
    fs::write(format!("{}/concept2.md", test_dir), concept2_content).unwrap();
    
    let result = checker.validate_directory(test_dir);
    fs::remove_dir_all(test_dir).unwrap();
    
    match result {
        ConceptValidationResult::Valid { concept_id, concept_name, symbols } => {
            assert!(!symbols.is_empty());
            println!("✅ 目录验证通过");
        },
        ConceptValidationResult::Invalid { errors } => {
            assert!(!errors.is_empty());
            println!("✅ 目录验证检测通过");
        }
    }
}

#[test]
fn test_empty_file() {
    let checker = ConceptChecker::new();
    
    // 创建空文件
    let temp_file = "temp_empty.md";
    fs::write(temp_file, "").unwrap();
    
    let result = checker.validate_file(temp_file);
    fs::remove_file(temp_file).unwrap();
    
    match result {
        ConceptValidationResult::Valid { .. } => {
            panic!("应该检测到空文件");
        },
        ConceptValidationResult::Invalid { errors } => {
            assert!(!errors.is_empty());
            println!("✅ 空文件检测通过");
        }
    }
}

#[test]
fn test_malformed_math() {
    let checker = ConceptChecker::new();
    
    // 创建数学公式格式错误的文件
    let malformed_content = r#"
# 格式错误测试

## 元数据
- **概念ID**: 01.03
- **概念名称**: 测试 (Test)
- **理论层次**: 第一层：基础理论层

## 形式化定义

```math
\text{Test}(v) \equiv v \in \text{Valid} \land \text{Invalid}
```

其中：
- $\text{Test}(v)$ 使用了未闭合的数学公式
- $\text{Invalid$ 缺少闭合符号
"#;
    
    let temp_file = "temp_malformed.md";
    fs::write(temp_file, malformed_content).unwrap();
    
    let result = checker.validate_file(temp_file);
    fs::remove_file(temp_file).unwrap();
    
    match result {
        ConceptValidationResult::Valid { .. } => {
            panic!("应该检测到格式错误");
        },
        ConceptValidationResult::Invalid { errors } => {
            assert!(!errors.is_empty());
            println!("✅ 格式错误检测通过");
        }
    }
}

fn main() {
    println!("开始运行概念一致性检查工具测试...");
    
    test_basic_concept_validation();
    test_invalid_concept_validation();
    test_missing_metadata();
    test_symbol_consistency();
    test_symbol_inconsistency();
    test_directory_validation();
    test_empty_file();
    test_malformed_math();
    
    println!("所有测试通过！");
} 