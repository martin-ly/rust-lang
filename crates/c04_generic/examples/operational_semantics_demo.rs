//! 小步操作语义 (Small-Step Operational Semantics) 演示
//! 小步操作语义 (Small-Step Operational Semantics) Demonstration of
//! - Move 语义：值ownershiptransfer
//! - 不可变借用 (&T)：共享只读访问
//! - borrowing (&T)：
//! - 可变借用 (&mut T)：独占读写访问
//! - borrowing (&mut T)：
//! - Drop 语义：资源释放
//! - Drop ：
//! - Drop 语义：资源Release
//!
//! 运行: cargo run --example operational_semantics_demo -p c04_generic

use std::collections::HashMap;

// ============================================================
// 抽象语法树 (AST)
// ============================================================

#[derive(Clone, Debug, PartialEq)]
enum Expr {
    Val(Value),              // 字面量值
    Var(String),             // 变量引用
    Let(String, Box<Expr>),  // let x = expr
    Move(String),            // move x
    Borrow(String),          // &x
    BorrowMut(String),       // &mut x
    Assign(String, Box<Expr>), // x = expr
    Seq(Box<Expr>, Box<Expr>), // expr1; expr2
}

#[derive(Clone, Debug, PartialEq)]
enum Value {
    Int(i32),
    Ref(String, Mutability), // 指向某变量的引用
    Unit,
}

#[derive(Clone, Debug, PartialEq)]
enum Mutability {
    Imm,
    Mut,
}

// ============================================================
// 运行时状态：栈帧 + 堆
// ============================================================

/// 栈上的变量绑定。每个绑定有一个**所有权状态**。
/// stack on variable 。**ownership state **。
#[derive(Clone, Debug, PartialEq)]
enum Ownership {
    Owned(Value),      // 拥有值
    Moved,             // 值已被移走
    Borrowed(Vec<Mutability>), // 被借用（记录借用类型）
}

struct State {
    stack: Vec<HashMap<String, Ownership>>,
    dropped: Vec<String>, // 记录已被 drop 的变量名（用于演示）
}

impl State {
    fn new() -> Self {
        Self {
            stack: vec![HashMap::new()],
            dropped: Vec::new(),
        }
    }

    fn current_frame(&mut self) -> &mut HashMap<String, Ownership> {
        self.stack.last_mut().unwrap()
    }

    fn lookup(&self, name: &str) -> Option<Ownership> {
        for frame in self.stack.iter().rev() {
            if let Some(binding) = frame.get(name) {
                return Some(binding.clone());
            }
        }
        None
    }

    fn bind(&mut self, name: &str, ownership: Ownership) {
        self.current_frame().insert(name.to_string(), ownership);
    }

    fn update(&mut self, name: &str, ownership: Ownership) -> Result<(), String> {
        for frame in self.stack.iter_mut().rev() {
            if frame.contains_key(name) {
                frame.insert(name.to_string(), ownership);
                return Ok(());
            }
        }
        Err(format!("变量 {} 未定义", name))
    }

    fn mark_moved(&mut self, name: &str) -> Result<(), String> {
        self.update(name, Ownership::Moved)
    }

    fn add_borrow(&mut self, name: &str, mutability: Mutability) -> Result<(), String> {
        match self.lookup(name) {
            Some(Ownership::Owned(_val)) => {
                self.update(name, Ownership::Borrowed(vec![mutability]))?;
                Ok(())
            }
            Some(Ownership::Borrowed(mut borrows)) => {
                // 检查借用规则：
                // - 如果已存在可变借用，不能再借
                // - 如果已有不可变借用，只能继续不可变借
                if borrows.contains(&Mutability::Mut) {
                    return Err(format!(
                        "借用检查失败: {} 已有 &mut 借用，不能再借",
                        name
                    ));
                }
                if mutability == Mutability::Mut {
                    return Err(format!(
                        "借用检查失败: {} 已有 & 借用，不能 &mut 借",
                        name
                    ));
                }
                borrows.push(mutability);
                self.update(name, Ownership::Borrowed(borrows))?;
                Ok(())
            }
            Some(Ownership::Moved) => Err(format!("借用检查失败: {} 已 move", name)),
            None => Err(format!("变量 {} 未定义", name)),
        }
    }

    #[allow(dead_code)]
    fn release_borrows(&mut self, name: &str) -> Result<(), String> {
        // 简化：将引用值恢复为 Owned
        // 实际语义中需要精确追踪每个引用的生命周期
        if let Some(Ownership::Borrowed(_)) = self.lookup(name) {
            // 这里无法恢复原值，因为 Move 语义下值已被消耗
            // 实际实现需要更复杂的存储模型
        }
        Ok(())
    }

    #[allow(dead_code)]
    fn drop_scope(&mut self) {
        if let Some(frame) = self.stack.pop() {
            for (name, ownership) in frame {
                if let Ownership::Owned(_) = ownership {
                    self.dropped.push(name);
                }
            }
        }
    }
}

// ============================================================
// 小步求值（一步）
// ============================================================

fn step(expr: Expr, state: &mut State) -> Result<(Expr, bool), String> {
    match expr {
        // 值已经是结果，不再规约
        Expr::Val(_) => Ok((expr, false)),

        // 变量引用：检查所有权状态
        Expr::Var(name) => match state.lookup(&name) {
            Some(Ownership::Owned(val)) => Ok((Expr::Val(val), true)),
            Some(Ownership::Moved) => Err(format!("使用已 move 的变量 {}", name)),
            Some(Ownership::Borrowed(_)) => {
                // 借用期间可以直接读取（简化模型）
                // 实际语义需要更复杂的处理
                Ok((Expr::Var(name), false))
            }
            None => Err(format!("变量 {} 未定义", name)),
        },

        // let x = val → Unit，并将 val 绑定到 x
        Expr::Let(name, rhs) => {
            if let Expr::Val(val) = *rhs {
                state.bind(&name, Ownership::Owned(val));
                Ok((Expr::Val(Value::Unit), true))
            } else {
                let (new_rhs, progressed) = step(*rhs, state)?;
                Ok((Expr::Let(name, Box::new(new_rhs)), progressed))
            }
        }

        // move x → val，并将 x 标记为 Moved
        Expr::Move(name) => match state.lookup(&name) {
            Some(Ownership::Owned(val)) => {
                state.mark_moved(&name)?;
                Ok((Expr::Val(val), true))
            }
            Some(Ownership::Moved) => Err(format!("move 已 move 的变量 {}", name)),
            Some(Ownership::Borrowed(_)) => Err(format!(
                "move 被借用的变量 {} — 需等待借用结束",
                name
            )),
            None => Err(format!("变量 {} 未定义", name)),
        },

        // &x → Ref(x, Imm)，检查借用规则
        Expr::Borrow(name) => {
            state.add_borrow(&name, Mutability::Imm)?;
            Ok((Expr::Val(Value::Ref(name.clone(), Mutability::Imm)), true))
        }

        // &mut x → Ref(x, Mut)，检查借用规则
        Expr::BorrowMut(name) => {
            state.add_borrow(&name, Mutability::Mut)?;
            Ok((Expr::Val(Value::Ref(name.clone(), Mutability::Mut)), true))
        }

        // x = val → Unit，要求 x 是 Owned 或 &mut
        Expr::Assign(name, rhs) => {
            if let Expr::Val(val) = *rhs {
                match state.lookup(&name) {
                    Some(Ownership::Owned(_)) | Some(Ownership::Borrowed(_)) => {
                        // 简化：直接更新值
                        // 实际语义中 &mut 赋值需要更复杂的处理
                        state.update(&name, Ownership::Owned(val))?;
                        Ok((Expr::Val(Value::Unit), true))
                    }
                    Some(Ownership::Moved) => {
                        Err(format!("给已 move 的变量 {} 赋值", name))
                    }
                    None => Err(format!("变量 {} 未定义", name)),
                }
            } else {
                let (new_rhs, progressed) = step(*rhs, state)?;
                Ok((Expr::Assign(name, Box::new(new_rhs)), progressed))
            }
        }

        // expr1; expr2 → 先求 expr1，再求 expr2
        Expr::Seq(e1, e2) => {
            if let Expr::Val(_) = *e1 {
                Ok((*e2, true)) // 丢弃 e1 的结果，继续 e2
            } else {
                let (new_e1, progressed) = step(*e1, state)?;
                Ok((Expr::Seq(Box::new(new_e1), e2), progressed))
            }
        }
    }
}

/// 完全求值（多步规约直到得到值或错误）
/// （to to or ）
fn eval(expr: Expr, state: &mut State) -> Result<Value, String> {
    let mut current = expr;
    loop {
        let (next, progressed) = step(current, state)?;
        if !progressed {
            if let Expr::Val(val) = next {
                return Ok(val);
            } else {
                return Err(format!(" stuck: {:?}", next));
            }
        }
        current = next;
    }
}

// ============================================================
// 演示程序
// ============================================================

fn demo_move_semantics() {
    println!("=== Move 语义演示 ===");
    let mut state = State::new();

    // let x = 42; let y = move x; // x 被移走
    let program = Expr::Seq(
        Box::new(Expr::Let("x".to_string(), Box::new(Expr::Val(Value::Int(42))))),
        Box::new(Expr::Seq(
            Box::new(Expr::Let(
                "y".to_string(),
                Box::new(Expr::Move("x".to_string())),
            )),
            Box::new(Expr::Var("y".to_string())),
        )),
    );

    match eval(program, &mut state) {
        Ok(val) => println!("✅ 求值结果: {:?}", val),
        Err(e) => println!("❌ 错误: {}", e),
    }

    // 尝试再次使用 x
    let mut state2 = State::new();
    let program2 = Expr::Seq(
        Box::new(Expr::Let("x".to_string(), Box::new(Expr::Val(Value::Int(42))))),
        Box::new(Expr::Seq(
            Box::new(Expr::Move("x".to_string())),
            Box::new(Expr::Var("x".to_string())), // 错误：x 已 move
        )),
    );

    match eval(program2, &mut state2) {
        Ok(val) => println!("意外成功: {:?}", val),
        Err(e) => println!("✅ 预期错误: {}", e),
    }
}

fn demo_borrow_semantics() {
    println!("\n=== 借用语义演示 ===");

    // let x = 42; let r = &x; *r
    let mut state = State::new();
    let program = Expr::Seq(
        Box::new(Expr::Let("x".to_string(), Box::new(Expr::Val(Value::Int(42))))),
        Box::new(Expr::Seq(
            Box::new(Expr::Let(
                "r".to_string(),
                Box::new(Expr::Borrow("x".to_string())),
            )),
            Box::new(Expr::Var("r".to_string())),
        )),
    );

    match eval(program, &mut state) {
        Ok(val) => println!("✅ 不可变借用成功: {:?}", val),
        Err(e) => println!("❌ 错误: {}", e),
    }

    // let x = 42; let r1 = &x; let r2 = &mut x; // 错误：已有 & 借用
    let mut state2 = State::new();
    let program2 = Expr::Seq(
        Box::new(Expr::Let("x".to_string(), Box::new(Expr::Val(Value::Int(42))))),
        Box::new(Expr::Seq(
            Box::new(Expr::Borrow("x".to_string())),
            Box::new(Expr::BorrowMut("x".to_string())),
        )),
    );

    match eval(program2, &mut state2) {
        Ok(val) => println!("意外成功: {:?}", val),
        Err(e) => println!("✅ 预期错误: {}", e),
    }

    // let x = 42; let r = &mut x; let r2 = &mut x; // 错误：已有 &mut 借用
    let mut state3 = State::new();
    let program3 = Expr::Seq(
        Box::new(Expr::Let("x".to_string(), Box::new(Expr::Val(Value::Int(42))))),
        Box::new(Expr::Seq(
            Box::new(Expr::BorrowMut("x".to_string())),
            Box::new(Expr::BorrowMut("x".to_string())),
        )),
    );

    match eval(program3, &mut state3) {
        Ok(val) => println!("意外成功: {:?}", val),
        Err(e) => println!("✅ 预期错误: {}", e),
    }
}

fn demo_assignment() {
    println!("\n=== 赋值语义演示 ===");

    // let x = 1; x = 2; x
    let mut state = State::new();
    let program = Expr::Seq(
        Box::new(Expr::Let("x".to_string(), Box::new(Expr::Val(Value::Int(1))))),
        Box::new(Expr::Seq(
            Box::new(Expr::Assign(
                "x".to_string(),
                Box::new(Expr::Val(Value::Int(2))),
            )),
            Box::new(Expr::Var("x".to_string())),
        )),
    );

    match eval(program, &mut state) {
        Ok(val) => println!("✅ 赋值后值: {:?}", val),
        Err(e) => println!("❌ 错误: {}", e),
    }
}

fn main() {
    demo_move_semantics();
    demo_borrow_semantics();
    demo_assignment();
    println!("\n🎉 操作语义演示完成！");
}
