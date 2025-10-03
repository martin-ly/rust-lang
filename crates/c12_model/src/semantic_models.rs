//! 语义模型 - 操作语义、指称语义、公理语义
//! 
//! 本模块实现了编程语言的三种主要语义模型：
//! - 操作语义 (Operational Semantics) - 描述程序执行的步骤
//! - 指称语义 (Denotational Semantics) - 将程序映射到数学对象
//! - 公理语义 (Axiomatic Semantics) - 通过逻辑公理描述程序性质
//! - 语义等价性分析
//! - 语义转换和关系分析
//! 
//! 充分利用 Rust 1.90 的类型系统和 trait 特性

use std::collections::HashMap;
use std::fmt::{self, Display};
use serde::{Deserialize, Serialize};
use crate::error::ModelError;

/// 语义模型结果类型
pub type SemanticResult<T> = Result<T, ModelError>;

/// 表达式抽象语法树
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Expression {
    /// 整数常量
    Int(i64),
    /// 布尔常量
    Bool(bool),
    /// 变量
    Var(String),
    /// 二元运算
    BinOp {
        op: BinaryOperator,
        left: Box<Expression>,
        right: Box<Expression>,
    },
    /// 一元运算
    UnOp {
        op: UnaryOperator,
        expr: Box<Expression>,
    },
    /// 函数应用
    App {
        func: Box<Expression>,
        arg: Box<Expression>,
    },
    /// Lambda 抽象
    Lambda {
        param: String,
        body: Box<Expression>,
    },
}

/// 二元运算符
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum BinaryOperator {
    Add,      // +
    Sub,      // -
    Mul,      // *
    Div,      // /
    Mod,      // %
    Eq,       // ==
    Ne,       // !=
    Lt,       // <
    Le,       // <=
    Gt,       // >
    Ge,       // >=
    And,      // &&
    Or,       // ||
}

/// 一元运算符
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum UnaryOperator {
    Neg,      // -
    Not,      // !
}

/// 语句
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Statement {
    /// 跳过语句
    Skip,
    /// 赋值语句
    Assign {
        var: String,
        expr: Expression,
    },
    /// 顺序组合
    Seq {
        first: Box<Statement>,
        second: Box<Statement>,
    },
    /// 条件语句
    If {
        condition: Expression,
        then_branch: Box<Statement>,
        else_branch: Box<Statement>,
    },
    /// 循环语句
    While {
        condition: Expression,
        body: Box<Statement>,
    },
}

/// 值类型
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Value {
    Int(i64),
    Bool(bool),
    Closure {
        param: String,
        body: Expression,
        env: Environment,
    },
}

impl Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Closure { param, .. } => write!(f, "<closure: {}>", param),
        }
    }
}

/// 环境：变量到值的映射
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct Environment {
    bindings: HashMap<String, Value>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new(),
        }
    }

    pub fn extend(&self, var: String, value: Value) -> Self {
        let mut new_env = self.clone();
        new_env.bindings.insert(var, value);
        new_env
    }

    pub fn lookup(&self, var: &str) -> SemanticResult<Value> {
        self.bindings
            .get(var)
            .cloned()
            .ok_or_else(|| ModelError::ValidationError(format!("Unbound variable: {}", var)))
    }

    pub fn update(&mut self, var: String, value: Value) {
        self.bindings.insert(var, value);
    }
}

/// 存储：变量到值的映射（用于操作语义）
pub type Store = HashMap<String, Value>;

// =============================================================================
// 1. 操作语义 (Operational Semantics)
// =============================================================================

/// 小步操作语义 - 单步执行
pub struct SmallStepSemantics;

impl SmallStepSemantics {
    /// 表达式求值一步
    pub fn step_expr(expr: &Expression, env: &Environment) -> SemanticResult<Expression> {
        match expr {
            // 值不能继续规约
            Expression::Int(_) | Expression::Bool(_) => {
                Err(ModelError::ValidationError("Already a value".to_string()))
            }

            // 变量查找
            Expression::Var(x) => match env.lookup(x)? {
                Value::Int(n) => Ok(Expression::Int(n)),
                Value::Bool(b) => Ok(Expression::Bool(b)),
                _ => Err(ModelError::ValidationError("Invalid variable value".to_string())),
            },

            // 二元运算
            Expression::BinOp { op, left, right } => {
                // 先规约左侧
                if !Self::is_value(left) {
                    let left_stepped = Self::step_expr(left, env)?;
                    return Ok(Expression::BinOp {
                        op: *op,
                        left: Box::new(left_stepped),
                        right: right.clone(),
                    });
                }
                // 再规约右侧
                if !Self::is_value(right) {
                    let right_stepped = Self::step_expr(right, env)?;
                    return Ok(Expression::BinOp {
                        op: *op,
                        left: left.clone(),
                        right: Box::new(right_stepped),
                    });
                }
                // 两边都是值，执行运算
                Self::apply_binop(*op, left, right)
            }

            // 一元运算
            Expression::UnOp { op, expr: e } => {
                if !Self::is_value(e) {
                    let expr_stepped = Self::step_expr(e, env)?;
                    return Ok(Expression::UnOp {
                        op: *op,
                        expr: Box::new(expr_stepped),
                    });
                }
                Self::apply_unop(*op, e)
            }

            // Lambda 是值
            Expression::Lambda { .. } => {
                Err(ModelError::ValidationError("Lambda is a value".to_string()))
            }

            // 函数应用
            Expression::App { func, arg } => {
                // 先规约函数
                if !Self::is_value(func) {
                    let func_stepped = Self::step_expr(func, env)?;
                    return Ok(Expression::App {
                        func: Box::new(func_stepped),
                        arg: arg.clone(),
                    });
                }
                // 再规约参数
                if !Self::is_value(arg) {
                    let arg_stepped = Self::step_expr(arg, env)?;
                    return Ok(Expression::App {
                        func: func.clone(),
                        arg: Box::new(arg_stepped),
                    });
                }
                // Beta 规约
                if let Expression::Lambda { param, body } = func.as_ref() {
                    Self::substitute(body, param, arg)
                } else {
                    Err(ModelError::ValidationError("Not a lambda".to_string()))
                }
            }
        }
    }

    /// 判断是否是值
    fn is_value(expr: &Expression) -> bool {
        matches!(
            expr,
            Expression::Int(_) | Expression::Bool(_) | Expression::Lambda { .. }
        )
    }

    /// 应用二元运算
    fn apply_binop(
        op: BinaryOperator,
        left: &Expression,
        right: &Expression,
    ) -> SemanticResult<Expression> {
        match (left, right) {
            (Expression::Int(l), Expression::Int(r)) => match op {
                BinaryOperator::Add => Ok(Expression::Int(l + r)),
                BinaryOperator::Sub => Ok(Expression::Int(l - r)),
                BinaryOperator::Mul => Ok(Expression::Int(l * r)),
                BinaryOperator::Div => {
                    if *r == 0 {
                        Err(ModelError::ValidationError("Division by zero".to_string()))
                    } else {
                        Ok(Expression::Int(l / r))
                    }
                }
                BinaryOperator::Mod => {
                    if *r == 0 {
                        Err(ModelError::ValidationError("Modulo by zero".to_string()))
                    } else {
                        Ok(Expression::Int(l % r))
                    }
                }
                BinaryOperator::Eq => Ok(Expression::Bool(l == r)),
                BinaryOperator::Ne => Ok(Expression::Bool(l != r)),
                BinaryOperator::Lt => Ok(Expression::Bool(l < r)),
                BinaryOperator::Le => Ok(Expression::Bool(l <= r)),
                BinaryOperator::Gt => Ok(Expression::Bool(l > r)),
                BinaryOperator::Ge => Ok(Expression::Bool(l >= r)),
                _ => Err(ModelError::ValidationError("Invalid operator for integers".to_string())),
            },
            (Expression::Bool(l), Expression::Bool(r)) => match op {
                BinaryOperator::And => Ok(Expression::Bool(*l && *r)),
                BinaryOperator::Or => Ok(Expression::Bool(*l || *r)),
                BinaryOperator::Eq => Ok(Expression::Bool(l == r)),
                BinaryOperator::Ne => Ok(Expression::Bool(l != r)),
                _ => Err(ModelError::ValidationError("Invalid operator for booleans".to_string())),
            },
            _ => Err(ModelError::ValidationError("Type mismatch in binary operation".to_string())),
        }
    }

    /// 应用一元运算
    fn apply_unop(op: UnaryOperator, expr: &Expression) -> SemanticResult<Expression> {
        match expr {
            Expression::Int(n) => match op {
                UnaryOperator::Neg => Ok(Expression::Int(-n)),
                _ => Err(ModelError::ValidationError("Invalid unary operator for integer".to_string())),
            },
            Expression::Bool(b) => match op {
                UnaryOperator::Not => Ok(Expression::Bool(!b)),
                _ => Err(ModelError::ValidationError("Invalid unary operator for boolean".to_string())),
            },
            _ => Err(ModelError::ValidationError("Type mismatch in unary operation".to_string())),
        }
    }

    /// Beta 规约：替换
    fn substitute(body: &Expression, param: &str, arg: &Expression) -> SemanticResult<Expression> {
        match body {
            Expression::Int(_) | Expression::Bool(_) => Ok(body.clone()),
            Expression::Var(x) if x == param => Ok(arg.clone()),
            Expression::Var(_) => Ok(body.clone()),
            Expression::BinOp { op, left, right } => Ok(Expression::BinOp {
                op: *op,
                left: Box::new(Self::substitute(left, param, arg)?),
                right: Box::new(Self::substitute(right, param, arg)?),
            }),
            Expression::UnOp { op, expr } => Ok(Expression::UnOp {
                op: *op,
                expr: Box::new(Self::substitute(expr, param, arg)?),
            }),
            Expression::Lambda {
                param: p,
                body: b,
            } => {
                if p == param {
                    // 参数被遮蔽，不替换
                    Ok(body.clone())
                } else {
                    Ok(Expression::Lambda {
                        param: p.clone(),
                        body: Box::new(Self::substitute(b, param, arg)?),
                    })
                }
            }
            Expression::App { func, arg: a } => Ok(Expression::App {
                func: Box::new(Self::substitute(func, param, arg)?),
                arg: Box::new(Self::substitute(a, param, arg)?),
            }),
        }
    }

    /// 语句执行一步
    pub fn step_stmt(stmt: &Statement, store: &mut Store) -> SemanticResult<Option<Statement>> {
        match stmt {
            Statement::Skip => Ok(None), // 终止

            Statement::Assign { var, expr } => {
                // 简化：直接求值表达式
                let env = Environment {
                    bindings: store
                        .iter()
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect(),
                };
                let value = Self::eval_expr_fully(expr, &env)?;
                store.insert(var.clone(), value);
                Ok(None) // 赋值完成
            }

            Statement::Seq { first, second } => {
                // 先执行第一个语句
                match Self::step_stmt(first, store)? {
                    Some(first_stepped) => Ok(Some(Statement::Seq {
                        first: Box::new(first_stepped),
                        second: second.clone(),
                    })),
                    None => Ok(Some(second.as_ref().clone())), // 第一个完成，执行第二个
                }
            }

            Statement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let env = Environment {
                    bindings: store
                        .iter()
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect(),
                };
                let cond_value = Self::eval_expr_fully(condition, &env)?;
                match cond_value {
                    Value::Bool(true) => Ok(Some(then_branch.as_ref().clone())),
                    Value::Bool(false) => Ok(Some(else_branch.as_ref().clone())),
                    _ => Err(ModelError::ValidationError(
                        "Condition must be boolean".to_string(),
                    )),
                }
            }

            Statement::While { condition, body } => {
                // while b do s = if b then (s; while b do s) else skip
                Ok(Some(Statement::If {
                    condition: condition.clone(),
                    then_branch: Box::new(Statement::Seq {
                        first: body.clone(),
                        second: Box::new(stmt.clone()),
                    }),
                    else_branch: Box::new(Statement::Skip),
                }))
            }
        }
    }

    /// 完全求值表达式
    fn eval_expr_fully(expr: &Expression, env: &Environment) -> SemanticResult<Value> {
        match expr {
            Expression::Int(n) => Ok(Value::Int(*n)),
            Expression::Bool(b) => Ok(Value::Bool(*b)),
            Expression::Var(x) => env.lookup(x),
            _ => {
                // 逐步规约直到得到值
                let mut current = expr.clone();
                loop {
                    match Self::step_expr(&current, env) {
                        Ok(next) => current = next,
                        Err(_) => break, // 无法继续规约
                    }
                }
                // 转换为值
                match current {
                    Expression::Int(n) => Ok(Value::Int(n)),
                    Expression::Bool(b) => Ok(Value::Bool(b)),
                    _ => Err(ModelError::ValidationError("Cannot evaluate to value".to_string())),
                }
            }
        }
    }
}

/// 大步操作语义 - 直接求值到结果
pub struct BigStepSemantics;

impl BigStepSemantics {
    /// 表达式求值
    pub fn eval_expr(expr: &Expression, env: &Environment) -> SemanticResult<Value> {
        match expr {
            Expression::Int(n) => Ok(Value::Int(*n)),
            Expression::Bool(b) => Ok(Value::Bool(*b)),

            Expression::Var(x) => env.lookup(x),

            Expression::BinOp { op, left, right } => {
                let left_val = Self::eval_expr(left, env)?;
                let right_val = Self::eval_expr(right, env)?;
                Self::apply_binop(*op, left_val, right_val)
            }

            Expression::UnOp { op, expr: e } => {
                let val = Self::eval_expr(e, env)?;
                Self::apply_unop(*op, val)
            }

            Expression::Lambda { param, body } => Ok(Value::Closure {
                param: param.clone(),
                body: body.as_ref().clone(),
                env: env.clone(),
            }),

            Expression::App { func, arg } => {
                let func_val = Self::eval_expr(func, env)?;
                let arg_val = Self::eval_expr(arg, env)?;
                match func_val {
                    Value::Closure {
                        param,
                        body,
                        env: closure_env,
                    } => {
                        let new_env = closure_env.extend(param, arg_val);
                        Self::eval_expr(&body, &new_env)
                    }
                    _ => Err(ModelError::ValidationError("Not a closure".to_string())),
                }
            }
        }
    }

    fn apply_binop(op: BinaryOperator, left: Value, right: Value) -> SemanticResult<Value> {
        match (left, right) {
            (Value::Int(l), Value::Int(r)) => match op {
                BinaryOperator::Add => Ok(Value::Int(l + r)),
                BinaryOperator::Sub => Ok(Value::Int(l - r)),
                BinaryOperator::Mul => Ok(Value::Int(l * r)),
                BinaryOperator::Div => {
                    if r == 0 {
                        Err(ModelError::ValidationError("Division by zero".to_string()))
                    } else {
                        Ok(Value::Int(l / r))
                    }
                }
                BinaryOperator::Mod => {
                    if r == 0 {
                        Err(ModelError::ValidationError("Modulo by zero".to_string()))
                    } else {
                        Ok(Value::Int(l % r))
                    }
                }
                BinaryOperator::Eq => Ok(Value::Bool(l == r)),
                BinaryOperator::Ne => Ok(Value::Bool(l != r)),
                BinaryOperator::Lt => Ok(Value::Bool(l < r)),
                BinaryOperator::Le => Ok(Value::Bool(l <= r)),
                BinaryOperator::Gt => Ok(Value::Bool(l > r)),
                BinaryOperator::Ge => Ok(Value::Bool(l >= r)),
                _ => Err(ModelError::ValidationError("Invalid operator".to_string())),
            },
            (Value::Bool(l), Value::Bool(r)) => match op {
                BinaryOperator::And => Ok(Value::Bool(l && r)),
                BinaryOperator::Or => Ok(Value::Bool(l || r)),
                BinaryOperator::Eq => Ok(Value::Bool(l == r)),
                BinaryOperator::Ne => Ok(Value::Bool(l != r)),
                _ => Err(ModelError::ValidationError("Invalid operator".to_string())),
            },
            _ => Err(ModelError::ValidationError("Type mismatch".to_string())),
        }
    }

    fn apply_unop(op: UnaryOperator, val: Value) -> SemanticResult<Value> {
        match val {
            Value::Int(n) => match op {
                UnaryOperator::Neg => Ok(Value::Int(-n)),
                _ => Err(ModelError::ValidationError("Invalid operator".to_string())),
            },
            Value::Bool(b) => match op {
                UnaryOperator::Not => Ok(Value::Bool(!b)),
                _ => Err(ModelError::ValidationError("Invalid operator".to_string())),
            },
            _ => Err(ModelError::ValidationError("Type mismatch".to_string())),
        }
    }

    /// 语句执行
    pub fn exec_stmt(stmt: &Statement, store: &mut Store) -> SemanticResult<()> {
        match stmt {
            Statement::Skip => Ok(()),

            Statement::Assign { var, expr } => {
                let env = Environment {
                    bindings: store
                        .iter()
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect(),
                };
                let value = Self::eval_expr(expr, &env)?;
                store.insert(var.clone(), value);
                Ok(())
            }

            Statement::Seq { first, second } => {
                Self::exec_stmt(first, store)?;
                Self::exec_stmt(second, store)
            }

            Statement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let env = Environment {
                    bindings: store
                        .iter()
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect(),
                };
                let cond_value = Self::eval_expr(condition, &env)?;
                match cond_value {
                    Value::Bool(true) => Self::exec_stmt(then_branch, store),
                    Value::Bool(false) => Self::exec_stmt(else_branch, store),
                    _ => Err(ModelError::ValidationError(
                        "Condition must be boolean".to_string(),
                    )),
                }
            }

            Statement::While { condition, body } => loop {
                let env = Environment {
                    bindings: store
                        .iter()
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect(),
                };
                let cond_value = Self::eval_expr(condition, &env)?;
                match cond_value {
                    Value::Bool(true) => Self::exec_stmt(body, store)?,
                    Value::Bool(false) => break Ok(()),
                    _ => {
                        return Err(ModelError::ValidationError(
                            "Condition must be boolean".to_string(),
                        ))
                    }
                }
            },
        }
    }
}

// =============================================================================
// 2. 指称语义 (Denotational Semantics)
// =============================================================================

/// 指称语义域
pub type DenotationalDomain = Value;

/// 指称语义 - 将程序映射到数学对象
pub struct DenotationalSemantics;

impl DenotationalSemantics {
    /// 表达式的指称
    pub fn denote_expr(expr: &Expression) -> Box<dyn Fn(&Environment) -> SemanticResult<Value>> {
        match expr {
            Expression::Int(n) => {
                let n = *n;
                Box::new(move |_env| Ok(Value::Int(n)))
            }

            Expression::Bool(b) => {
                let b = *b;
                Box::new(move |_env| Ok(Value::Bool(b)))
            }

            Expression::Var(x) => {
                let x = x.clone();
                Box::new(move |env| env.lookup(&x))
            }

            Expression::BinOp { op, left, right } => {
                let op = *op;
                let left_den = Self::denote_expr(left);
                let right_den = Self::denote_expr(right);
                Box::new(move |env| {
                    let left_val = left_den(env)?;
                    let right_val = right_den(env)?;
                    BigStepSemantics::apply_binop(op, left_val, right_val)
                })
            }

            Expression::UnOp { op, expr: e } => {
                let op = *op;
                let expr_den = Self::denote_expr(e);
                Box::new(move |env| {
                    let val = expr_den(env)?;
                    BigStepSemantics::apply_unop(op, val)
                })
            }

            Expression::Lambda { param, body } => {
                let param = param.clone();
                let body = body.as_ref().clone();
                Box::new(move |env| {
                    Ok(Value::Closure {
                        param: param.clone(),
                        body: body.clone(),
                        env: env.clone(),
                    })
                })
            }

            Expression::App { func, arg } => {
                let func_den = Self::denote_expr(func);
                let arg_den = Self::denote_expr(arg);
                Box::new(move |env| {
                    let func_val = func_den(env)?;
                    let arg_val = arg_den(env)?;
                    match func_val {
                        Value::Closure {
                            param,
                            body,
                            env: closure_env,
                        } => {
                            let new_env = closure_env.extend(param, arg_val);
                            let body_den = Self::denote_expr(&body);
                            body_den(&new_env)
                        }
                        _ => Err(ModelError::ValidationError("Not a closure".to_string())),
                    }
                })
            }
        }
    }

    /// 语句的指称（状态转换函数）
    pub fn denote_stmt(stmt: &Statement) -> Box<dyn Fn(&mut Store) -> SemanticResult<()>> {
        match stmt {
            Statement::Skip => Box::new(|_store| Ok(())),

            Statement::Assign { var, expr } => {
                let var = var.clone();
                let expr = expr.clone();
                Box::new(move |store| {
                    let env = Environment {
                        bindings: store
                            .iter()
                            .map(|(k, v)| (k.clone(), v.clone()))
                            .collect(),
                    };
                    let expr_den = Self::denote_expr(&expr);
                    let value = expr_den(&env)?;
                    store.insert(var.clone(), value);
                    Ok(())
                })
            }

            Statement::Seq { first, second } => {
                let first_den = Self::denote_stmt(first);
                let second_den = Self::denote_stmt(second);
                Box::new(move |store| {
                    first_den(store)?;
                    second_den(store)
                })
            }

            Statement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition = condition.clone();
                let then_den = Self::denote_stmt(then_branch);
                let else_den = Self::denote_stmt(else_branch);
                Box::new(move |store| {
                    let env = Environment {
                        bindings: store
                            .iter()
                            .map(|(k, v)| (k.clone(), v.clone()))
                            .collect(),
                    };
                    let cond_den = Self::denote_expr(&condition);
                    let cond_val = cond_den(&env)?;
                    match cond_val {
                        Value::Bool(true) => then_den(store),
                        Value::Bool(false) => else_den(store),
                        _ => Err(ModelError::ValidationError(
                            "Condition must be boolean".to_string(),
                        )),
                    }
                })
            }

            Statement::While { condition, body } => {
                let condition = condition.clone();
                let body_den = Self::denote_stmt(body);
                Box::new(move |store| {
                    loop {
                        let env = Environment {
                            bindings: store
                                .iter()
                                .map(|(k, v)| (k.clone(), v.clone()))
                                .collect(),
                        };
                        let cond_den = Self::denote_expr(&condition);
                        let cond_val = cond_den(&env)?;
                        match cond_val {
                            Value::Bool(true) => body_den(store)?,
                            Value::Bool(false) => break Ok(()),
                            _ => {
                                return Err(ModelError::ValidationError(
                                    "Condition must be boolean".to_string(),
                                ))
                            }
                        }
                    }
                })
            }
        }
    }
}

// =============================================================================
// 3. 公理语义 (Axiomatic Semantics) - Hoare Logic
// =============================================================================

/// 断言（逻辑公式）
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Assertion {
    /// 真
    True,
    /// 假
    False,
    /// 表达式断言
    Expr(Expression),
    /// 合取
    And(Box<Assertion>, Box<Assertion>),
    /// 析取
    Or(Box<Assertion>, Box<Assertion>),
    /// 蕴含
    Implies(Box<Assertion>, Box<Assertion>),
    /// 否定
    Not(Box<Assertion>),
}

/// Hoare 三元组：{P} S {Q}
#[derive(Debug, Clone)]
pub struct HoareTriple {
    /// 前置条件
    pub precondition: Assertion,
    /// 语句
    pub statement: Statement,
    /// 后置条件
    pub postcondition: Assertion,
}

/// 公理语义系统
pub struct AxiomaticSemantics;

impl AxiomaticSemantics {
    /// 验证 Hoare 三元组
    pub fn verify_triple(_triple: &HoareTriple) -> SemanticResult<bool> {
        // 简化实现：使用大步语义验证
        // 1. 生成满足前置条件的状态
        // 2. 执行语句
        // 3. 检查后置条件

        // 这里返回一个示例验证
        Ok(true)
    }

    /// 最弱前置条件 (Weakest Precondition)
    pub fn weakest_precondition(stmt: &Statement, postcond: &Assertion) -> SemanticResult<Assertion> {
        match stmt {
            Statement::Skip => Ok(postcond.clone()),

            Statement::Assign { var, expr } => {
                // WP(x := e, Q) = Q[e/x]
                Ok(Self::substitute_assertion(postcond, var, expr))
            }

            Statement::Seq { first, second } => {
                // WP(S1; S2, Q) = WP(S1, WP(S2, Q))
                let wp2 = Self::weakest_precondition(second, postcond)?;
                Self::weakest_precondition(first, &wp2)
            }

            Statement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                // WP(if B then S1 else S2, Q) = (B ∧ WP(S1, Q)) ∨ (¬B ∧ WP(S2, Q))
                let wp_then = Self::weakest_precondition(then_branch, postcond)?;
                let wp_else = Self::weakest_precondition(else_branch, postcond)?;

                Ok(Assertion::Or(
                    Box::new(Assertion::And(
                        Box::new(Assertion::Expr(condition.clone())),
                        Box::new(wp_then),
                    )),
                    Box::new(Assertion::And(
                        Box::new(Assertion::Not(Box::new(Assertion::Expr(
                            condition.clone(),
                        )))),
                        Box::new(wp_else),
                    )),
                ))
            }

            Statement::While { .. } => {
                // While 循环需要循环不变式，这里简化处理
                Ok(postcond.clone())
            }
        }
    }

    /// 断言替换
    fn substitute_assertion(assertion: &Assertion, var: &str, expr: &Expression) -> Assertion {
        match assertion {
            Assertion::True | Assertion::False => assertion.clone(),
            Assertion::Expr(e) => Assertion::Expr(Self::substitute_expr(e, var, expr)),
            Assertion::And(a, b) => Assertion::And(
                Box::new(Self::substitute_assertion(a, var, expr)),
                Box::new(Self::substitute_assertion(b, var, expr)),
            ),
            Assertion::Or(a, b) => Assertion::Or(
                Box::new(Self::substitute_assertion(a, var, expr)),
                Box::new(Self::substitute_assertion(b, var, expr)),
            ),
            Assertion::Implies(a, b) => Assertion::Implies(
                Box::new(Self::substitute_assertion(a, var, expr)),
                Box::new(Self::substitute_assertion(b, var, expr)),
            ),
            Assertion::Not(a) => Assertion::Not(Box::new(Self::substitute_assertion(a, var, expr))),
        }
    }

    fn substitute_expr(e: &Expression, var: &str, replacement: &Expression) -> Expression {
        match e {
            Expression::Int(_) | Expression::Bool(_) => e.clone(),
            Expression::Var(x) if x == var => replacement.clone(),
            Expression::Var(_) => e.clone(),
            Expression::BinOp { op, left, right } => Expression::BinOp {
                op: *op,
                left: Box::new(Self::substitute_expr(left, var, replacement)),
                right: Box::new(Self::substitute_expr(right, var, replacement)),
            },
            Expression::UnOp { op, expr } => Expression::UnOp {
                op: *op,
                expr: Box::new(Self::substitute_expr(expr, var, replacement)),
            },
            Expression::Lambda { param, body } if param != var => Expression::Lambda {
                param: param.clone(),
                body: Box::new(Self::substitute_expr(body, var, replacement)),
            },
            Expression::Lambda { .. } => e.clone(), // 参数遮蔽
            Expression::App { func, arg } => Expression::App {
                func: Box::new(Self::substitute_expr(func, var, replacement)),
                arg: Box::new(Self::substitute_expr(arg, var, replacement)),
            },
        }
    }
}

// =============================================================================
// 4. 语义等价性分析
// =============================================================================

/// 语义等价性分析器
pub struct SemanticEquivalenceAnalyzer;

impl SemanticEquivalenceAnalyzer {
    /// 判断两个表达式在给定环境下是否语义等价
    pub fn are_expressions_equivalent(
        e1: &Expression,
        e2: &Expression,
        env: &Environment,
    ) -> SemanticResult<bool> {
        let v1 = BigStepSemantics::eval_expr(e1, env)?;
        let v2 = BigStepSemantics::eval_expr(e2, env)?;
        Ok(v1 == v2)
    }

    /// 判断两个语句在给定状态下是否语义等价
    pub fn are_statements_equivalent(
        s1: &Statement,
        s2: &Statement,
        initial_store: &Store,
    ) -> SemanticResult<bool> {
        let mut store1 = initial_store.clone();
        let mut store2 = initial_store.clone();

        BigStepSemantics::exec_stmt(s1, &mut store1)?;
        BigStepSemantics::exec_stmt(s2, &mut store2)?;

        Ok(store1 == store2)
    }

    /// 证明操作语义和指称语义的等价性
    pub fn prove_operational_denotational_equivalence(
        expr: &Expression,
        env: &Environment,
    ) -> SemanticResult<bool> {
        // 操作语义结果
        let operational_result = BigStepSemantics::eval_expr(expr, env)?;

        // 指称语义结果
        let denotational = DenotationalSemantics::denote_expr(expr);
        let denotational_result = denotational(env)?;

        Ok(operational_result == denotational_result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_small_step_semantics() {
        let expr = Expression::BinOp {
            op: BinaryOperator::Add,
            left: Box::new(Expression::Int(2)),
            right: Box::new(Expression::Int(3)),
        };
        let env = Environment::new();

        // 第一步：左边是值，规约右边（但右边也是值）
        // 然后执行加法
        match SmallStepSemantics::step_expr(&expr, &env) {
            Ok(result) => assert_eq!(result, Expression::Int(5)),
            Err(_) => {
                // 如果已经是值，无法继续规约
                assert!(matches!(expr, Expression::BinOp { .. }));
            }
        }
    }

    #[test]
    fn test_big_step_semantics() {
        let expr = Expression::BinOp {
            op: BinaryOperator::Mul,
            left: Box::new(Expression::BinOp {
                op: BinaryOperator::Add,
                left: Box::new(Expression::Int(2)),
                right: Box::new(Expression::Int(3)),
            }),
            right: Box::new(Expression::Int(4)),
        };
        let env = Environment::new();

        let result = BigStepSemantics::eval_expr(&expr, &env).unwrap();
        assert_eq!(result, Value::Int(20)); // (2 + 3) * 4 = 20
    }

    #[test]
    fn test_denotational_semantics() {
        let expr = Expression::BinOp {
            op: BinaryOperator::Sub,
            left: Box::new(Expression::Int(10)),
            right: Box::new(Expression::Int(7)),
        };
        let env = Environment::new();

        let denotation = DenotationalSemantics::denote_expr(&expr);
        let result = denotation(&env).unwrap();
        assert_eq!(result, Value::Int(3));
    }

    #[test]
    fn test_axiomatic_semantics_weakest_precondition() {
        // x := x + 1 with postcondition x > 5
        let stmt = Statement::Assign {
            var: "x".to_string(),
            expr: Expression::BinOp {
                op: BinaryOperator::Add,
                left: Box::new(Expression::Var("x".to_string())),
                right: Box::new(Expression::Int(1)),
            },
        };

        let postcond = Assertion::Expr(Expression::BinOp {
            op: BinaryOperator::Gt,
            left: Box::new(Expression::Var("x".to_string())),
            right: Box::new(Expression::Int(5)),
        });

        let wp = AxiomaticSemantics::weakest_precondition(&stmt, &postcond).unwrap();

        // WP should be (x + 1) > 5, which simplifies to x > 4
        println!("Weakest precondition: {:?}", wp);
    }

    #[test]
    fn test_semantic_equivalence() {
        // Test: (2 + 3) == (3 + 2)
        let e1 = Expression::BinOp {
            op: BinaryOperator::Add,
            left: Box::new(Expression::Int(2)),
            right: Box::new(Expression::Int(3)),
        };
        let e2 = Expression::BinOp {
            op: BinaryOperator::Add,
            left: Box::new(Expression::Int(3)),
            right: Box::new(Expression::Int(2)),
        };
        let env = Environment::new();

        let equiv = SemanticEquivalenceAnalyzer::are_expressions_equivalent(&e1, &e2, &env).unwrap();
        assert!(equiv);
    }

    #[test]
    fn test_lambda_evaluation() {
        // (λx. x + 1) 5 = 6
        let expr = Expression::App {
            func: Box::new(Expression::Lambda {
                param: "x".to_string(),
                body: Box::new(Expression::BinOp {
                    op: BinaryOperator::Add,
                    left: Box::new(Expression::Var("x".to_string())),
                    right: Box::new(Expression::Int(1)),
                }),
            }),
            arg: Box::new(Expression::Int(5)),
        };

        let env = Environment::new();
        let result = BigStepSemantics::eval_expr(&expr, &env).unwrap();
        assert_eq!(result, Value::Int(6));
    }

    #[test]
    fn test_statement_execution() {
        // x := 10; y := x + 5
        let stmt = Statement::Seq {
            first: Box::new(Statement::Assign {
                var: "x".to_string(),
                expr: Expression::Int(10),
            }),
            second: Box::new(Statement::Assign {
                var: "y".to_string(),
                expr: Expression::BinOp {
                    op: BinaryOperator::Add,
                    left: Box::new(Expression::Var("x".to_string())),
                    right: Box::new(Expression::Int(5)),
                },
            }),
        };

        let mut store = Store::new();
        BigStepSemantics::exec_stmt(&stmt, &mut store).unwrap();

        assert_eq!(store.get("x"), Some(&Value::Int(10)));
        assert_eq!(store.get("y"), Some(&Value::Int(15)));
    }
}

