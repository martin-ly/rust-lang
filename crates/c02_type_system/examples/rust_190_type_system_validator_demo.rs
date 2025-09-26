//! Rust 1.90 类型系统验证工具演示
//!
//! 本示例展示了 Rust 1.90 中的类型系统验证特性

use c02_type_system::type_system_validator::*;
use std::collections::HashMap;

fn main() {
    println!("=== Rust 1.90 类型系统验证工具演示程序 ===\n");
    
    // 运行所有类型系统验证演示
    demonstrate_type_system_validation();
    
    // 运行交互式演示
    interactive_type_validation_demo();
    
    // 运行高级类型验证演示
    advanced_type_validation_demo();
}

/// 交互式类型验证演示
fn interactive_type_validation_demo() {
    println!("\n=== 交互式类型验证演示 ===\n");
    
    // 1. 交互式类型创建和验证
    println!("1. 交互式类型创建和验证:");
    interactive_type_creation_and_validation();
    
    // 2. 交互式类型兼容性检查
    println!("\n2. 交互式类型兼容性检查:");
    interactive_type_compatibility_check();
    
    // 3. 交互式生命周期验证
    println!("\n3. 交互式生命周期验证:");
    interactive_lifetime_validation();
    
    // 4. 交互式泛型类型验证
    println!("\n4. 交互式泛型类型验证:");
    interactive_generic_type_validation();
    
    // 5. 交互式类型推断
    println!("\n5. 交互式类型推断:");
    interactive_type_inference();
}

/// 交互式类型创建和验证
fn interactive_type_creation_and_validation() {
    let mut validator = TypeValidator::new();
    
    // 添加自定义验证规则
    validator.add_validation_rule(
        "numeric_type_validation".to_string(),
        "验证数值类型".to_string(),
        |type_, _env| {
            match type_ {
                Type::Primitive(PrimitiveType::I32 | PrimitiveType::F64) => {
                    ValidationResult {
                        valid: true,
                        message: "Numeric type is valid".to_string(),
                        suggestions: Vec::new(),
                        severity: ValidationSeverity::Info,
                    }
                },
                Type::Primitive(PrimitiveType::Bool) => {
                    ValidationResult {
                        valid: false,
                        message: "Boolean type is not numeric".to_string(),
                        suggestions: vec!["Use i32 or f64 for numeric operations".to_string()],
                        severity: ValidationSeverity::Warning,
                    }
                },
                _ => ValidationResult {
                    valid: false,
                    message: "Type is not numeric".to_string(),
                    suggestions: vec!["Use a primitive numeric type".to_string()],
                    severity: ValidationSeverity::Error,
                },
            }
        },
    );
    
    // 创建各种类型进行验证
    let types_to_validate = vec![
        ("整数类型", Type::Primitive(PrimitiveType::I32)),
        ("浮点类型", Type::Primitive(PrimitiveType::F64)),
        ("布尔类型", Type::Primitive(PrimitiveType::Bool)),
        ("字符串类型", Type::Primitive(PrimitiveType::String)),
        ("字符类型", Type::Primitive(PrimitiveType::Char)),
        ("复合类型", Type::Composite(CompositeType::Tuple(vec![
            Type::Primitive(PrimitiveType::I32),
            Type::Primitive(PrimitiveType::String),
        ]))),
        ("引用类型", Type::Reference(ReferenceType {
            lifetime: None,
            mutable: false,
            target: Box::new(Type::Primitive(PrimitiveType::I32)),
        })),
    ];
    
    for (type_name, type_) in types_to_validate {
        println!("  验证 {}:", type_name);
        let results = validator.validate_type(&type_);
        
        for result in results {
            let status = if result.valid { "✅" } else { "❌" };
            let severity_icon = match result.severity {
                ValidationSeverity::Info => "ℹ️",
                ValidationSeverity::Warning => "⚠️",
                ValidationSeverity::Error => "❌",
                ValidationSeverity::Critical => "🚨",
            };
            println!("    {} {} {:?}: {}", status, severity_icon, result.severity, result.message);
            
            if !result.suggestions.is_empty() {
                for suggestion in result.suggestions {
                    println!("      💡 建议: {}", suggestion);
                }
            }
        }
        println!();
    }
}

/// 交互式类型兼容性检查
fn interactive_type_compatibility_check() {
    let validator = TypeValidator::new();
    
    // 定义类型兼容性测试用例
    let compatibility_tests = vec![
        // 相同类型
        ("i32 -> i32", Type::Primitive(PrimitiveType::I32), Type::Primitive(PrimitiveType::I32)),
        ("f64 -> f64", Type::Primitive(PrimitiveType::F64), Type::Primitive(PrimitiveType::F64)),
        ("bool -> bool", Type::Primitive(PrimitiveType::Bool), Type::Primitive(PrimitiveType::Bool)),
        
        // 数值类型转换
        ("i32 -> f64", Type::Primitive(PrimitiveType::I32), Type::Primitive(PrimitiveType::F64)),
        ("f64 -> i32", Type::Primitive(PrimitiveType::F64), Type::Primitive(PrimitiveType::I32)),
        
        // 不兼容类型
        ("bool -> i32", Type::Primitive(PrimitiveType::Bool), Type::Primitive(PrimitiveType::I32)),
        ("string -> i32", Type::Primitive(PrimitiveType::String), Type::Primitive(PrimitiveType::I32)),
        ("char -> f64", Type::Primitive(PrimitiveType::Char), Type::Primitive(PrimitiveType::F64)),
        
        // 复合类型
        ("tuple -> tuple", 
         Type::Composite(CompositeType::Tuple(vec![Type::Primitive(PrimitiveType::I32)])),
         Type::Composite(CompositeType::Tuple(vec![Type::Primitive(PrimitiveType::I32)]))),
        
        // 引用类型
        ("&i32 -> &i32",
         Type::Reference(ReferenceType {
             lifetime: None,
             mutable: false,
             target: Box::new(Type::Primitive(PrimitiveType::I32)),
         }),
         Type::Reference(ReferenceType {
             lifetime: None,
             mutable: false,
             target: Box::new(Type::Primitive(PrimitiveType::I32)),
         })),
    ];
    
    for (test_name, from_type, to_type) in compatibility_tests {
        let result = validator.validate_compatibility(&from_type, &to_type);
        let status = if result.valid { "✅" } else { "❌" };
        let severity_icon = match result.severity {
            ValidationSeverity::Info => "ℹ️",
            ValidationSeverity::Warning => "⚠️",
            ValidationSeverity::Error => "❌",
            ValidationSeverity::Critical => "🚨",
        };
        
        println!("  {} {} {:?}: {}", status, severity_icon, test_name, result.message);
        
        if !result.suggestions.is_empty() {
            for suggestion in result.suggestions {
                println!("    💡 建议: {}", suggestion);
            }
        }
    }
}

/// 交互式生命周期验证
#[allow(dead_code)]
#[allow(unused_mut)]    
fn interactive_lifetime_validation() {
    let mut validator = TypeValidator::new();
    
    // 定义生命周期
    let lifetimes = vec![
        ("'a", LifetimeType {
            name: "a".to_string(),
            constraints: Vec::new(),
        }),
        ("'b", LifetimeType {
            name: "b".to_string(),
            constraints: vec![LifetimeType {
                name: "a".to_string(),
                constraints: Vec::new(),
            }],
        }),
        ("'static", LifetimeType {
            name: "static".to_string(),
            constraints: Vec::new(),
        }),
    ];
    
    // 添加生命周期定义
    for (name, lifetime) in &lifetimes {
        validator.add_lifetime_definition(name.to_string(), lifetime.clone());
    }
    
    // 验证生命周期
    for (name, lifetime) in lifetimes {
        println!("  验证生命周期 {}:", name);
        let result = validator.validate_lifetime(&lifetime);
        
        let status = if result.valid { "✅" } else { "❌" };
        let severity_icon = match result.severity {
            ValidationSeverity::Info => "ℹ️",
            ValidationSeverity::Warning => "⚠️",
            ValidationSeverity::Error => "❌",
            ValidationSeverity::Critical => "🚨",
        };
        
        println!("    {} {} {:?}: {}", status, severity_icon, result.severity, result.message);
        
        if !result.suggestions.is_empty() {
            for suggestion in result.suggestions {
                println!("      💡 建议: {}", suggestion);
            }
        }
    }
    
    // 测试带生命周期的引用类型
    println!("\n  测试带生命周期的引用类型:");
    let lifetime_ref_types = vec![
        ("&'a i32", Type::Reference(ReferenceType {
            lifetime: Some(LifetimeType {
                name: "a".to_string(),
                constraints: Vec::new(),
            }),
            mutable: false,
            target: Box::new(Type::Primitive(PrimitiveType::I32)),
        })),
        ("&'b mut String", Type::Reference(ReferenceType {
            lifetime: Some(LifetimeType {
                name: "b".to_string(),
                constraints: Vec::new(),
            }),
            mutable: true,
            target: Box::new(Type::Primitive(PrimitiveType::String)),
        })),
    ];
    
    for (type_name, type_) in lifetime_ref_types {
        println!("    验证 {}:", type_name);
        let results = validator.validate_type(&type_);
        
        for result in results {
            let status = if result.valid { "✅" } else { "❌" };
            println!("      {} {:?}: {}", status, result.severity, result.message);
        }
    }
}

/// 交互式泛型类型验证
#[allow(dead_code)]
#[allow(unused_mut)]    
fn interactive_generic_type_validation() {
    let mut validator = TypeValidator::new();
    
    // 定义各种泛型类型
    let generic_types = vec![
        ("Vec<T> (空参数)", GenericType {
            name: "Vec".to_string(),
            parameters: Vec::new(),
            constraints: Vec::new(),
        }),
        ("Vec<i32>", GenericType {
            name: "Vec".to_string(),
            parameters: vec![Type::Primitive(PrimitiveType::I32)],
            constraints: Vec::new(),
        }),
        ("HashMap<String, i32>", GenericType {
            name: "HashMap".to_string(),
            parameters: vec![
                Type::Primitive(PrimitiveType::String),
                Type::Primitive(PrimitiveType::I32),
            ],
            constraints: Vec::new(),
        }),
        ("Option<Result<T, E>>", GenericType {
            name: "Option".to_string(),
            parameters: vec![Type::Generic(GenericType {
                name: "Result".to_string(),
                parameters: vec![
                    Type::Unknown,
                    Type::Unknown,
                ],
                constraints: Vec::new(),
            })],
            constraints: Vec::new(),
        }),
        ("Box<dyn Trait>", GenericType {
            name: "Box".to_string(),
            parameters: vec![Type::Generic(GenericType {
                name: "dyn".to_string(),
                parameters: vec![Type::Unknown],
                constraints: vec![TypeConstraint::Trait("Trait".to_string())],
            })],
            constraints: Vec::new(),
        }),
    ];
    
    for (type_name, generic_type) in generic_types {
        println!("  验证泛型类型 {}:", type_name);
        let result = validator.validate_generic_type(&generic_type);
        
        let status = if result.valid { "✅" } else { "❌" };
        let severity_icon = match result.severity {
            ValidationSeverity::Info => "ℹ️",
            ValidationSeverity::Warning => "⚠️",
            ValidationSeverity::Error => "❌",
            ValidationSeverity::Critical => "🚨",
        };
        
        println!("    {} {} {:?}: {}", status, severity_icon, result.severity, result.message);
        
        if !result.suggestions.is_empty() {
            for suggestion in result.suggestions {
                println!("      💡 建议: {}", suggestion);
            }
        }
    }
    
    // 测试泛型类型兼容性
    println!("\n  测试泛型类型兼容性:");
    let vec_i32 = Type::Generic(GenericType {
        name: "Vec".to_string(),
        parameters: vec![Type::Primitive(PrimitiveType::I32)],
        constraints: Vec::new(),
    });
    
    let vec_f64 = Type::Generic(GenericType {
        name: "Vec".to_string(),
        parameters: vec![Type::Primitive(PrimitiveType::F64)],
        constraints: Vec::new(),
    });
    
    let compatibility_tests = vec![
        ("Vec<i32> -> Vec<i32>", vec_i32.clone(), vec_i32.clone()),
        ("Vec<i32> -> Vec<f64>", vec_i32, vec_f64),
    ];
    
    for (test_name, from, to) in compatibility_tests {
        let result = validator.validate_compatibility(&from, &to);
        let status = if result.valid { "✅" } else { "❌" };
        println!("    {} {}: {}", status, test_name, result.message);
    }
}

/// 交互式类型推断
#[allow(dead_code)]
fn interactive_type_inference() {
    let inferencer = TypeInferencer::new();
    
    // 添加函数定义
    let function_definitions = vec![
        ("add", Type::Function(FunctionType {
            parameters: vec![
                Type::Primitive(PrimitiveType::I32),
                Type::Primitive(PrimitiveType::I32),
            ],
            return_type: Box::new(Type::Primitive(PrimitiveType::I32)),
            lifetime_params: Vec::new(),
        })),
        ("multiply", Type::Function(FunctionType {
            parameters: vec![
                Type::Primitive(PrimitiveType::F64),
                Type::Primitive(PrimitiveType::F64),
            ],
            return_type: Box::new(Type::Primitive(PrimitiveType::F64)),
            lifetime_params: Vec::new(),
        })),
        ("is_positive", Type::Function(FunctionType {
            parameters: vec![Type::Primitive(PrimitiveType::I32)],
            return_type: Box::new(Type::Primitive(PrimitiveType::Bool)),
            lifetime_params: Vec::new(),
        })),
    ];
    
    for (name, func_type) in function_definitions {
        inferencer.add_type_definition(name.to_string(), func_type);
    }
    
    // 添加变量类型
    let variable_types = vec![
        ("x", Type::Primitive(PrimitiveType::I32)),
        ("y", Type::Primitive(PrimitiveType::F64)),
        ("flag", Type::Primitive(PrimitiveType::Bool)),
    ];
    
    for (name, var_type) in variable_types {
        inferencer.add_variable_type(name.to_string(), var_type);
    }
    
    // 测试表达式类型推断
    let expressions = vec![
        ("字面量 42", Expression::Literal(Literal::Integer(42))),
        ("字面量 3.14", Expression::Literal(Literal::Float(3.14))),
        ("字面量 true", Expression::Literal(Literal::Boolean(true))),
        ("字面量 'hello'", Expression::Literal(Literal::String("hello".to_string()))),
        ("字面量 'A'", Expression::Literal(Literal::Char('A'))),
        
        ("变量 x", Expression::Variable("x".to_string())),
        ("变量 y", Expression::Variable("y".to_string())),
        ("变量 flag", Expression::Variable("flag".to_string())),
        ("变量 unknown", Expression::Variable("unknown".to_string())),
        
        ("10 + 20", Expression::BinaryOp {
            left: Box::new(Expression::Literal(Literal::Integer(10))),
            operator: BinaryOperator::Add,
            right: Box::new(Expression::Literal(Literal::Integer(20))),
        }),
        
        ("3.14 * 2.0", Expression::BinaryOp {
            left: Box::new(Expression::Literal(Literal::Float(3.14))),
            operator: BinaryOperator::Mul,
            right: Box::new(Expression::Literal(Literal::Float(2.0))),
        }),
        
        ("10 == 20", Expression::BinaryOp {
            left: Box::new(Expression::Literal(Literal::Integer(10))),
            operator: BinaryOperator::Eq,
            right: Box::new(Expression::Literal(Literal::Integer(20))),
        }),
        
        ("true && false", Expression::BinaryOp {
            left: Box::new(Expression::Literal(Literal::Boolean(true))),
            operator: BinaryOperator::And,
            right: Box::new(Expression::Literal(Literal::Boolean(false))),
        }),
        
        ("!true", Expression::UnaryOp {
            operator: UnaryOperator::Not,
            operand: Box::new(Expression::Literal(Literal::Boolean(true))),
        }),
        
        ("-42", Expression::UnaryOp {
            operator: UnaryOperator::Neg,
            operand: Box::new(Expression::Literal(Literal::Integer(42))),
        }),
        
        ("add(5, 3)", Expression::FunctionCall {
            name: "add".to_string(),
            arguments: vec![
                Expression::Literal(Literal::Integer(5)),
                Expression::Literal(Literal::Integer(3)),
            ],
        }),
        
        ("multiply(2.5, 4.0)", Expression::FunctionCall {
            name: "multiply".to_string(),
            arguments: vec![
                Expression::Literal(Literal::Float(2.5)),
                Expression::Literal(Literal::Float(4.0)),
            ],
        }),
        
        ("is_positive(10)", Expression::FunctionCall {
            name: "is_positive".to_string(),
            arguments: vec![Expression::Literal(Literal::Integer(10))],
        }),
        
        ("if true then 1 else 0", Expression::If {
            condition: Box::new(Expression::Literal(Literal::Boolean(true))),
            then_branch: Box::new(Expression::Literal(Literal::Integer(1))),
            else_branch: Box::new(Expression::Literal(Literal::Integer(0))),
        }),
    ];
    
    for (expr_name, expr) in expressions {
        match inferencer.infer_expression_type(&expr) {
            Ok(type_) => {
                println!("  ✅ {} 推断类型: {}", expr_name, format_type(&type_));
            },
            Err(e) => {
                println!("  ❌ {} 推断失败: {}", expr_name, e);
            },
        }
    }
    
    // 显示推断统计
    let stats = inferencer.get_stats();
    println!("\n  推断统计:");
    println!("    总推断次数: {}", stats.total_inferences);
    println!("    成功推断: {}", stats.successful_inferences);
    println!("    失败推断: {}", stats.failed_inferences);
    println!("    按类型分布: {:?}", stats.inferences_by_type);
}

/// 高级类型验证演示
#[allow(dead_code)]
#[allow(unused_mut)]   
#[allow(unused_variables)]
fn advanced_type_validation_demo() {
    println!("\n=== 高级类型验证演示 ===\n");
    
    // 1. 复杂类型系统演示
    println!("1. 复杂类型系统演示:");
    let mut validator = TypeValidator::new();
    
    // 创建复杂的类型层次结构
    let complex_types = vec![
        ("嵌套元组", Type::Composite(CompositeType::Tuple(vec![
            Type::Composite(CompositeType::Tuple(vec![
                Type::Primitive(PrimitiveType::I32),
                Type::Primitive(PrimitiveType::String),
            ])),
            Type::Primitive(PrimitiveType::Bool),
        ]))),
        
        ("数组类型", Type::Composite(CompositeType::Array {
            element: Box::new(Type::Primitive(PrimitiveType::I32)),
            size: Some(10),
        })),
        
        ("切片类型", Type::Composite(CompositeType::Slice(
            Box::new(Type::Primitive(PrimitiveType::String))
        ))),
        
        ("结构体类型", Type::Composite(CompositeType::Struct {
            name: "User".to_string(),
            fields: {
                let mut fields = HashMap::new();
                fields.insert("id".to_string(), Type::Primitive(PrimitiveType::I32));
                fields.insert("name".to_string(), Type::Primitive(PrimitiveType::String));
                fields.insert("active".to_string(), Type::Primitive(PrimitiveType::Bool));
                fields
            },
        })),
        
        ("枚举类型", Type::Composite(CompositeType::Enum {
            name: "Status".to_string(),
            variants: {
                let mut variants = HashMap::new();
                variants.insert("Active".to_string(), Vec::new());
                variants.insert("Inactive".to_string(), Vec::new());
                variants.insert("Pending".to_string(), vec![Type::Primitive(PrimitiveType::String)]);
                variants
            },
        })),
    ];
    
    for (type_name, type_) in complex_types {
        println!("  验证 {}:", type_name);
        let results = validator.validate_type(&type_);
        
        for result in results {
            let status = if result.valid { "✅" } else { "❌" };
            println!("    {} {:?}: {}", status, result.severity, result.message);
        }
    }
    
    // 2. 类型系统性能测试
    println!("\n2. 类型系统性能测试:");
    let start = std::time::Instant::now();
    
    for i in 0..1000 {
        let type_ = Type::Primitive(PrimitiveType::I32);
        let _ = validator.validate_type(&type_);
    }
    
    let duration = start.elapsed();
    println!("  验证1000个类型耗时: {:?}", duration);
    println!("  平均每个类型: {:?}", duration / 1000);
    
    // 3. 类型推断性能测试
    println!("\n3. 类型推断性能测试:");
    let inferencer = TypeInferencer::new();
    
    let start = std::time::Instant::now();
    
    for i in 0..1000 {
        let expr = Expression::Literal(Literal::Integer(i));
        let _ = inferencer.infer_expression_type(&expr);
    }
    
    let duration = start.elapsed();
    println!("  推断1000个表达式耗时: {:?}", duration);
    println!("  平均每个表达式: {:?}", duration / 1000);
    
    // 4. 类型系统统计
    println!("\n4. 类型系统统计:");
    let stats = validator.get_stats();
    println!("  验证统计:");
    println!("    总验证次数: {}", stats.total_validations);
    println!("    成功验证: {}", stats.successful_validations);
    println!("    失败验证: {}", stats.failed_validations);
    println!("    按类型分布: {:?}", stats.validations_by_type);
    println!("    按严重程度分布: {:?}", stats.validations_by_severity);
    
    let inference_stats = inferencer.get_stats();
    println!("  推断统计:");
    println!("    总推断次数: {}", inference_stats.total_inferences);
    println!("    成功推断: {}", inference_stats.successful_inferences);
    println!("    失败推断: {}", inference_stats.failed_inferences);
}

/// 格式化类型显示
fn format_type(type_: &Type) -> String {
    match type_ {
        Type::Primitive(p) => format!("{:?}", p),
        Type::Composite(c) => format!("{:?}", c),
        Type::Generic(g) => format!("{}<{}>", g.name, 
            g.parameters.iter().map(|p| format_type(p)).collect::<Vec<_>>().join(", ")),
        Type::Function(f) => format!("fn({}) -> {}", 
            f.parameters.iter().map(|p| format_type(p)).collect::<Vec<_>>().join(", "),
            format_type(&f.return_type)),
        Type::Reference(r) => {
            let lifetime = if let Some(l) = &r.lifetime {
                format!("'{} ", l.name)
            } else {
                String::new()
            };
            let mutability = if r.mutable { "mut " } else { "" };
            format!("&{}{}{}", lifetime, mutability, format_type(&r.target))
        },
        Type::Lifetime(l) => format!("'{}", l.name),
        Type::Unknown => "?".to_string(),
    }
}
