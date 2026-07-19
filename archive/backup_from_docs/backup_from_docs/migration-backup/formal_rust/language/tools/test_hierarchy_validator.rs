use std::fs;
use std::path::Path;
use hierarchy_validator::{HierarchyValidator, ValidationResult};

#[test]
fn test_basic_hierarchy_validation() {
    let validator = HierarchyValidator::new();
    
    // 创建测试目录结构
    let test_dir = "test_hierarchy";
    fs::create_dir_all(test_dir).unwrap();
    
    // 创建符合层次结构的文件
    let layer1_content = r#"
# 基础理论层

## 元数据
- **理论层次**: 第一层：基础理论层
- **概念ID**: 01.01
"#;
    
    let layer2_content = r#"
# 语言特性形式化层

## 元数据
- **理论层次**: 第二层：语言特性形式化层
- **概念ID**: 02.01
"#;
    
    let layer3_content = r#"
# 安全性与正确性证明层

## 元数据
- **理论层次**: 第三层：安全性与正确性证明层
- **概念ID**: 03.01
"#;
    
    let layer4_content = r#"
# 实践应用层

## 元数据
- **理论层次**: 第四层：实践应用层
- **概念ID**: 04.01
"#;
    
    fs::write(format!("{}/layer1.md", test_dir), layer1_content).unwrap();
    fs::write(format!("{}/layer2.md", test_dir), layer2_content).unwrap();
    fs::write(format!("{}/layer3.md", test_dir), layer3_content).unwrap();
    fs::write(format!("{}/layer4.md", test_dir), layer4_content).unwrap();
    
    // 验证层次结构
    let result = validator.validate_directory(test_dir);
    
    // 清理测试文件
    fs::remove_dir_all(test_dir).unwrap();
    
    match result {
        ValidationResult::Valid { valid_files, invalid_files } => {
            assert_eq!(valid_files.len(), 4);
            assert_eq!(invalid_files.len(), 0);
            println!("✅ 基本层次验证通过");
        },
        ValidationResult::Invalid { errors } => {
            panic!("层次验证失败: {:?}", errors);
        }
    }
}

#[test]
fn test_invalid_hierarchy_validation() {
    let validator = HierarchyValidator::new();
    
    // 创建测试目录结构
    let test_dir = "test_invalid_hierarchy";
    fs::create_dir_all(test_dir).unwrap();
    
    // 创建不符合层次结构的文件
    let invalid_content = r#"
# 无效文件

## 元数据
- **理论层次**: 第五层：不存在的层次
- **概念ID**: 05.01
"#;
    
    let missing_layer_content = r#"
# 缺少层次信息

## 元数据
- **概念ID**: 01.01
"#;
    
    fs::write(format!("{}/invalid.md", test_dir), invalid_content).unwrap();
    fs::write(format!("{}/missing_layer.md", test_dir), missing_layer_content).unwrap();
    
    // 验证层次结构
    let result = validator.validate_directory(test_dir);
    
    // 清理测试文件
    fs::remove_dir_all(test_dir).unwrap();
    
    match result {
        ValidationResult::Valid { valid_files, invalid_files } => {
            assert_eq!(valid_files.len(), 0);
            assert_eq!(invalid_files.len(), 2);
            println!("✅ 无效层次验证通过");
        },
        ValidationResult::Invalid { errors } => {
            assert!(!errors.is_empty());
            println!("✅ 无效层次检测通过");
        }
    }
}

#[test]
fn test_mixed_hierarchy_validation() {
    let validator = HierarchyValidator::new();
    
    // 创建测试目录结构
    let test_dir = "test_mixed_hierarchy";
    fs::create_dir_all(test_dir).unwrap();
    
    // 创建混合内容
    let valid_content = r#"
# 有效文件

## 元数据
- **理论层次**: 第二层：语言特性形式化层
- **概念ID**: 02.01
"#;
    
    let invalid_content = r#"
# 无效文件

## 元数据
- **理论层次**: 第六层：不存在的层次
- **概念ID**: 06.01
"#;
    
    fs::write(format!("{}/valid.md", test_dir), valid_content).unwrap();
    fs::write(format!("{}/invalid.md", test_dir), invalid_content).unwrap();
    
    // 验证层次结构
    let result = validator.validate_directory(test_dir);
    
    // 清理测试文件
    fs::remove_dir_all(test_dir).unwrap();
    
    match result {
        ValidationResult::Valid { valid_files, invalid_files } => {
            assert_eq!(valid_files.len(), 1);
            assert_eq!(invalid_files.len(), 1);
            println!("✅ 混合层次验证通过");
        },
        ValidationResult::Invalid { errors } => {
            assert!(!errors.is_empty());
            println!("✅ 混合层次检测通过");
        }
    }
}

#[test]
fn test_empty_directory() {
    let validator = HierarchyValidator::new();
    
    // 创建空目录
    let test_dir = "test_empty";
    fs::create_dir_all(test_dir).unwrap();
    
    // 验证空目录
    let result = validator.validate_directory(test_dir);
    
    // 清理测试文件
    fs::remove_dir_all(test_dir).unwrap();
    
    match result {
        ValidationResult::Valid { valid_files, invalid_files } => {
            assert_eq!(valid_files.len(), 0);
            assert_eq!(invalid_files.len(), 0);
            println!("✅ 空目录验证通过");
        },
        ValidationResult::Invalid { errors } => {
            assert!(errors.is_empty());
            println!("✅ 空目录检测通过");
        }
    }
}

#[test]
fn test_nested_directory_structure() {
    let validator = HierarchyValidator::new();
    
    // 创建嵌套目录结构
    let test_dir = "test_nested";
    fs::create_dir_all(format!("{}/subdir1", test_dir)).unwrap();
    fs::create_dir_all(format!("{}/subdir2", test_dir)).unwrap();
    
    // 创建有效文件
    let layer1_content = r#"
# 基础理论层

## 元数据
- **理论层次**: 第一层：基础理论层
- **概念ID**: 01.01
"#;
    
    let layer2_content = r#"
# 语言特性形式化层

## 元数据
- **理论层次**: 第二层：语言特性形式化层
- **概念ID**: 02.01
"#;
    
    fs::write(format!("{}/layer1.md", test_dir), layer1_content).unwrap();
    fs::write(format!("{}/subdir1/layer2.md", test_dir), layer2_content).unwrap();
    
    // 验证嵌套目录
    let result = validator.validate_directory(test_dir);
    
    // 清理测试文件
    fs::remove_dir_all(test_dir).unwrap();
    
    match result {
        ValidationResult::Valid { valid_files, invalid_files } => {
            assert_eq!(valid_files.len(), 2);
            assert_eq!(invalid_files.len(), 0);
            println!("✅ 嵌套目录验证通过");
        },
        ValidationResult::Invalid { errors } => {
            panic!("嵌套目录验证失败: {:?}", errors);
        }
    }
}

#[test]
fn test_file_validation() {
    let validator = HierarchyValidator::new();
    
    // 测试有效文件
    let valid_content = r#"
# 有效文件

## 元数据
- **理论层次**: 第三层：安全性与正确性证明层
- **概念ID**: 03.01
"#;
    
    let temp_file = "temp_valid.md";
    fs::write(temp_file, valid_content).unwrap();
    
    let result = validator.validate_file(temp_file);
    fs::remove_file(temp_file).unwrap();
    
    assert!(result.is_valid());
    println!("✅ 文件验证通过");
}

#[test]
fn test_invalid_file_validation() {
    let validator = HierarchyValidator::new();
    
    // 测试无效文件
    let invalid_content = r#"
# 无效文件

## 元数据
- **理论层次**: 第七层：不存在的层次
- **概念ID**: 07.01
"#;
    
    let temp_file = "temp_invalid.md";
    fs::write(temp_file, invalid_content).unwrap();
    
    let result = validator.validate_file(temp_file);
    fs::remove_file(temp_file).unwrap();
    
    assert!(!result.is_valid());
    println!("✅ 无效文件检测通过");
}

#[test]
fn test_missing_layer_info() {
    let validator = HierarchyValidator::new();
    
    // 测试缺少层次信息的文件
    let missing_content = r#"
# 缺少层次信息

## 元数据
- **概念ID**: 01.01
"#;
    
    let temp_file = "temp_missing.md";
    fs::write(temp_file, missing_content).unwrap();
    
    let result = validator.validate_file(temp_file);
    fs::remove_file(temp_file).unwrap();
    
    assert!(!result.is_valid());
    println!("✅ 缺少层次信息检测通过");
}

fn main() {
    println!("开始运行层次框架验证工具测试...");
    
    test_basic_hierarchy_validation();
    test_invalid_hierarchy_validation();
    test_mixed_hierarchy_validation();
    test_empty_directory();
    test_nested_directory_structure();
    test_file_validation();
    test_invalid_file_validation();
    test_missing_layer_info();
    
    println!("所有测试通过！");
} 