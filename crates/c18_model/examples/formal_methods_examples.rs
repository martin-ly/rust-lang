//! 形式化方法的Rust实现示例
//! 
//! 本文件展示了如何使用Rust实现形式化方法，
//! 包括状态机、时序逻辑、模型检查等。

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

/// 状态机状态
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    pub id: String,
    pub properties: HashMap<String, bool>,
}

impl State {
    pub fn new(id: String) -> Self {
        Self {
            id,
            properties: HashMap::new(),
        }
    }

    pub fn with_property(mut self, key: String, value: bool) -> Self {
        self.properties.insert(key, value);
        self
    }

    pub fn get_property(&self, key: &str) -> Option<bool> {
        self.properties.get(key).copied()
    }
}

/// 状态转换
#[derive(Debug, Clone)]
pub struct Transition {
    pub from: String,
    pub to: String,
    pub event: String,
    pub condition: Option<String>,
    pub action: Option<String>,
}

impl Transition {
    pub fn new(from: String, to: String, event: String) -> Self {
        Self {
            from,
            to,
            event,
            condition: None,
            action: None,
        }
    }

    pub fn with_condition(mut self, condition: String) -> Self {
        self.condition = Some(condition);
        self
    }

    pub fn with_action(mut self, action: String) -> Self {
        self.action = Some(action);
        self
    }
}

/// 有限状态机
#[derive(Debug, Clone)]
pub struct FiniteStateMachine {
    pub states: HashMap<String, State>,
    pub transitions: Vec<Transition>,
    pub initial_state: String,
    pub current_state: String,
}

impl FiniteStateMachine {
    pub fn new(initial_state: String) -> Self {
        let mut states = HashMap::new();
        let initial = State::new(initial_state.clone());
        states.insert(initial_state.clone(), initial);
        
        Self {
            states,
            transitions: Vec::new(),
            initial_state: initial_state.clone(),
            current_state: initial_state,
        }
    }

    pub fn add_state(&mut self, state: State) {
        self.states.insert(state.id.clone(), state);
    }

    pub fn add_transition(&mut self, transition: Transition) {
        self.transitions.push(transition);
    }

    pub fn get_current_state(&self) -> &State {
        &self.states[&self.current_state]
    }

    pub fn can_transition(&self, event: &str) -> bool {
        self.transitions.iter().any(|t| {
            t.from == self.current_state && t.event == event
        })
    }

    pub fn transition(&mut self, event: &str) -> Result<(), String> {
        if let Some(transition) = self.transitions.iter().find(|t| {
            t.from == self.current_state && t.event == event
        }) {
            self.current_state = transition.to.clone();
            Ok(())
        } else {
            Err(format!("无法从状态 '{}' 通过事件 '{}' 进行转换", self.current_state, event))
        }
    }

    pub fn reset(&mut self) {
        self.current_state = self.initial_state.clone();
    }

    /// 检查状态机是否满足不变式
    pub fn check_invariant(&self, invariant: &str) -> bool {
        match invariant {
            "always_safe" => {
                // 检查所有状态是否都是安全的
                self.states.values().all(|state| {
                    state.get_property("safe").unwrap_or(true)
                })
            },
            "eventually_goal" => {
                // 检查是否存在从当前状态到目标状态的路径
                self.reachable_states().contains("goal")
            },
            _ => false,
        }
    }

    /// 计算可达状态
    pub fn reachable_states(&self) -> HashSet<String> {
        let mut reachable = HashSet::new();
        let mut queue = VecDeque::new();
        
        queue.push_back(self.current_state.clone());
        reachable.insert(self.current_state.clone());
        
        while let Some(current) = queue.pop_front() {
            for transition in &self.transitions {
                if transition.from == current && !reachable.contains(&transition.to) {
                    reachable.insert(transition.to.clone());
                    queue.push_back(transition.to.clone());
                }
            }
        }
        
        reachable
    }

    /// 检查死锁
    pub fn has_deadlock(&self) -> bool {
        let reachable = self.reachable_states();
        
        for state_id in &reachable {
            let has_outgoing = self.transitions.iter().any(|t| t.from == *state_id);
            if !has_outgoing && *state_id != "final" {
                return true;
            }
        }
        
        false
    }
}

/// 时序逻辑公式
#[derive(Debug, Clone)]
pub enum TemporalFormula {
    /// 原子命题
    Atomic(String),
    /// 否定
    Not(Box<TemporalFormula>),
    /// 合取
    And(Box<TemporalFormula>, Box<TemporalFormula>),
    /// 析取
    Or(Box<TemporalFormula>, Box<TemporalFormula>),
    /// 蕴含
    Implies(Box<TemporalFormula>, Box<TemporalFormula>),
    /// 总是 (G)
    Always(Box<TemporalFormula>),
    /// 最终 (F)
    Eventually(Box<TemporalFormula>),
    /// 下一个 (X)
    Next(Box<TemporalFormula>),
    /// 直到 (U)
    Until(Box<TemporalFormula>, Box<TemporalFormula>),
}

impl TemporalFormula {
    /// 创建原子命题
    pub fn atomic(prop: String) -> Self {
        TemporalFormula::Atomic(prop)
    }

    /// 创建否定
    pub fn not(formula: TemporalFormula) -> Self {
        TemporalFormula::Not(Box::new(formula))
    }

    /// 创建合取
    pub fn and(left: TemporalFormula, right: TemporalFormula) -> Self {
        TemporalFormula::And(Box::new(left), Box::new(right))
    }

    /// 创建析取
    pub fn or(left: TemporalFormula, right: TemporalFormula) -> Self {
        TemporalFormula::Or(Box::new(left), Box::new(right))
    }

    /// 创建蕴含
    pub fn implies(left: TemporalFormula, right: TemporalFormula) -> Self {
        TemporalFormula::Implies(Box::new(left), Box::new(right))
    }

    /// 创建总是
    pub fn always(formula: TemporalFormula) -> Self {
        TemporalFormula::Always(Box::new(formula))
    }

    /// 创建最终
    pub fn eventually(formula: TemporalFormula) -> Self {
        TemporalFormula::Eventually(Box::new(formula))
    }

    /// 创建下一个
    pub fn next(formula: TemporalFormula) -> Self {
        TemporalFormula::Next(Box::new(formula))
    }

    /// 创建直到
    pub fn until(left: TemporalFormula, right: TemporalFormula) -> Self {
        TemporalFormula::Until(Box::new(left), Box::new(right))
    }
}

impl fmt::Display for TemporalFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TemporalFormula::Atomic(prop) => write!(f, "{}", prop),
            TemporalFormula::Not(formula) => write!(f, "¬({})", formula),
            TemporalFormula::And(left, right) => write!(f, "({}) ∧ ({})", left, right),
            TemporalFormula::Or(left, right) => write!(f, "({}) ∨ ({})", left, right),
            TemporalFormula::Implies(left, right) => write!(f, "({}) → ({})", left, right),
            TemporalFormula::Always(formula) => write!(f, "G({})", formula),
            TemporalFormula::Eventually(formula) => write!(f, "F({})", formula),
            TemporalFormula::Next(formula) => write!(f, "X({})", formula),
            TemporalFormula::Until(left, right) => write!(f, "({}) U ({})", left, right),
        }
    }
}

/// 模型检查器
#[derive(Debug)]
pub struct ModelChecker {
    pub fsm: FiniteStateMachine,
}

impl ModelChecker {
    pub fn new(fsm: FiniteStateMachine) -> Self {
        Self { fsm }
    }

    /// 检查公式在状态机中是否成立
    pub fn check(&mut self, formula: &TemporalFormula) -> bool {
        self.check_formula(formula, &self.fsm.current_state, &mut HashSet::new())
    }

    /// 递归检查公式
    fn check_formula(&self, formula: &TemporalFormula, state: &str, visited: &mut HashSet<String>) -> bool {
        if visited.contains(state) {
            return false; // 避免无限循环
        }
        visited.insert(state.to_string());

        match formula {
            TemporalFormula::Atomic(prop) => {
                self.fsm.states.get(state)
                    .and_then(|s| s.get_property(prop))
                    .unwrap_or(false)
            },
            TemporalFormula::Not(f) => !self.check_formula(f, state, visited),
            TemporalFormula::And(left, right) => {
                self.check_formula(left, state, visited) && self.check_formula(right, state, visited)
            },
            TemporalFormula::Or(left, right) => {
                self.check_formula(left, state, visited) || self.check_formula(right, state, visited)
            },
            TemporalFormula::Implies(left, right) => {
                !self.check_formula(left, state, visited) || self.check_formula(right, state, visited)
            },
            TemporalFormula::Always(f) => {
                // 检查所有可达状态
                let reachable = self.fsm.reachable_states();
                reachable.iter().all(|s| {
                    let mut new_visited = visited.clone();
                    self.check_formula(f, s, &mut new_visited)
                })
            },
            TemporalFormula::Eventually(f) => {
                // 检查是否存在可达状态满足公式
                let reachable = self.fsm.reachable_states();
                reachable.iter().any(|s| {
                    let mut new_visited = visited.clone();
                    self.check_formula(f, s, &mut new_visited)
                })
            },
            TemporalFormula::Next(f) => {
                // 检查所有直接后继状态
                let successors: Vec<String> = self.fsm.transitions.iter()
                    .filter(|t| t.from == state)
                    .map(|t| t.to.clone())
                    .collect();
                
                if successors.is_empty() {
                    false
                } else {
                    successors.iter().all(|s| {
                        let mut new_visited = visited.clone();
                        self.check_formula(f, s, &mut new_visited)
                    })
                }
            },
            TemporalFormula::Until(left, right) => {
                // 检查是否存在路径满足 left U right
                self.check_until(left, right, state, visited)
            },
        }
    }

    /// 检查 Until 公式
    fn check_until(&self, left: &TemporalFormula, right: &TemporalFormula, 
                   state: &str, visited: &mut HashSet<String>) -> bool {
        // 首先检查 right 是否在当前状态成立
        if self.check_formula(right, state, visited) {
            return true;
        }

        // 检查 left 是否在当前状态成立
        if !self.check_formula(left, state, visited) {
            return false;
        }

        // 检查所有后继状态
        let successors: Vec<String> = self.fsm.transitions.iter()
            .filter(|t| t.from == state)
            .map(|t| t.to.clone())
            .collect();

        successors.iter().any(|s| {
            let mut new_visited = visited.clone();
            self.check_until(left, right, s, &mut new_visited)
        })
    }

    /// 生成反例
    pub fn generate_counterexample(&mut self, formula: &TemporalFormula) -> Option<Vec<String>> {
        if self.check(formula) {
            return None;
        }

        // 简化的反例生成
        let mut counterexample = Vec::new();
        let mut current_state = self.fsm.current_state.clone();
        
        counterexample.push(current_state.clone());
        
        // 尝试找到违反公式的路径
        for _ in 0..10 { // 限制搜索深度
            if let Some(transition) = self.fsm.transitions.iter()
                .find(|t| t.from == current_state) {
                current_state = transition.to.clone();
                counterexample.push(current_state.clone());
            } else {
                break;
            }
        }
        
        Some(counterexample)
    }
}

/// 进程代数项
#[derive(Debug, Clone)]
pub enum ProcessTerm {
    /// 空进程
    Nil,
    /// 动作前缀
    Prefix(String, Box<ProcessTerm>),
    /// 选择
    Choice(Box<ProcessTerm>, Box<ProcessTerm>),
    /// 并行组合
    Parallel(Box<ProcessTerm>, Box<ProcessTerm>),
    /// 顺序组合
    Sequence(Box<ProcessTerm>, Box<ProcessTerm>),
}

impl ProcessTerm {
    pub fn nil() -> Self {
        ProcessTerm::Nil
    }

    pub fn prefix(action: String, process: ProcessTerm) -> Self {
        ProcessTerm::Prefix(action, Box::new(process))
    }

    pub fn choice(left: ProcessTerm, right: ProcessTerm) -> Self {
        ProcessTerm::Choice(Box::new(left), Box::new(right))
    }

    pub fn parallel(left: ProcessTerm, right: ProcessTerm) -> Self {
        ProcessTerm::Parallel(Box::new(left), Box::new(right))
    }

    pub fn sequence(left: ProcessTerm, right: ProcessTerm) -> Self {
        ProcessTerm::Sequence(Box::new(left), Box::new(right))
    }
}

impl fmt::Display for ProcessTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProcessTerm::Nil => write!(f, "0"),
            ProcessTerm::Prefix(action, process) => write!(f, "{}.{}", action, process),
            ProcessTerm::Choice(left, right) => write!(f, "({}) + ({})", left, right),
            ProcessTerm::Parallel(left, right) => write!(f, "({}) | ({})", left, right),
            ProcessTerm::Sequence(left, right) => write!(f, "({}); ({})", left, right),
        }
    }
}

/// 进程代数解释器
#[derive(Debug)]
pub struct ProcessAlgebraInterpreter {
    pub processes: HashMap<String, ProcessTerm>,
}

impl ProcessAlgebraInterpreter {
    pub fn new() -> Self {
        Self {
            processes: HashMap::new(),
        }
    }

    pub fn define_process(&mut self, name: String, process: ProcessTerm) {
        self.processes.insert(name, process);
    }

    /// 执行进程项
    pub fn execute(&self, process: &ProcessTerm) -> Vec<String> {
        let mut trace = Vec::new();
        self.execute_with_trace(process, &mut trace);
        trace
    }

    fn execute_with_trace(&self, process: &ProcessTerm, trace: &mut Vec<String>) {
        match process {
            ProcessTerm::Nil => {
                // 空进程，什么都不做
            },
            ProcessTerm::Prefix(action, next) => {
                trace.push(action.clone());
                self.execute_with_trace(next, trace);
            },
            ProcessTerm::Choice(left, right) => {
                // 随机选择一个分支
                if fastrand::bool() {
                    self.execute_with_trace(left, trace);
                } else {
                    self.execute_with_trace(right, trace);
                }
            },
            ProcessTerm::Parallel(left, right) => {
                // 并行执行（简化实现）
                let mut left_trace = Vec::new();
                let mut right_trace = Vec::new();
                
                self.execute_with_trace(left, &mut left_trace);
                self.execute_with_trace(right, &mut right_trace);
                
                // 交错执行
                let max_len = left_trace.len().max(right_trace.len());
                for i in 0..max_len {
                    if i < left_trace.len() {
                        trace.push(format!("L:{}", left_trace[i]));
                    }
                    if i < right_trace.len() {
                        trace.push(format!("R:{}", right_trace[i]));
                    }
                }
            },
            ProcessTerm::Sequence(left, right) => {
                self.execute_with_trace(left, trace);
                self.execute_with_trace(right, trace);
            },
        }
    }

    /// 检查进程等价性（简化实现）
    pub fn are_equivalent(&self, p1: &ProcessTerm, p2: &ProcessTerm) -> bool {
        // 简化的等价性检查：比较执行轨迹
        let _trace1 = self.execute(p1);
        let _trace2 = self.execute(p2);
        
        // 多次执行以确保随机性
        for _ in 0..10 {
            let t1 = self.execute(p1);
            let t2 = self.execute(p2);
            if t1 != t2 {
                return false;
            }
        }
        
        true
    }
}

fn main() {
    println!("=== Rust形式化方法示例 ===\n");

    // 1. 有限状态机示例
    println!("1. 有限状态机");
    let mut fsm = FiniteStateMachine::new("idle".to_string());
    
    // 添加状态
    fsm.add_state(State::new("idle".to_string()).with_property("safe".to_string(), true));
    fsm.add_state(State::new("working".to_string()).with_property("safe".to_string(), true));
    fsm.add_state(State::new("error".to_string()).with_property("safe".to_string(), false));
    fsm.add_state(State::new("goal".to_string()).with_property("safe".to_string(), true));
    
    // 添加转换
    fsm.add_transition(Transition::new("idle".to_string(), "working".to_string(), "start".to_string()));
    fsm.add_transition(Transition::new("working".to_string(), "idle".to_string(), "stop".to_string()));
    fsm.add_transition(Transition::new("working".to_string(), "error".to_string(), "fail".to_string()));
    fsm.add_transition(Transition::new("error".to_string(), "idle".to_string(), "reset".to_string()));
    fsm.add_transition(Transition::new("working".to_string(), "goal".to_string(), "complete".to_string()));
    
    println!("   初始状态: {}", fsm.current_state);
    println!("   可达状态: {:?}", fsm.reachable_states());
    println!("   有死锁: {}", fsm.has_deadlock());
    println!("   满足不变式 'always_safe': {}", fsm.check_invariant("always_safe"));
    println!();

    // 2. 时序逻辑示例
    println!("2. 时序逻辑模型检查");
    let mut checker = ModelChecker::new(fsm.clone());
    
    // 创建时序逻辑公式
    let safe_prop = TemporalFormula::atomic("safe".to_string());
    let always_safe = TemporalFormula::always(safe_prop.clone());
    let eventually_goal = TemporalFormula::eventually(TemporalFormula::atomic("goal".to_string()));
    
    println!("   公式: {}", always_safe);
    println!("   检查结果: {}", checker.check(&always_safe));
    
    println!("   公式: {}", eventually_goal);
    println!("   检查结果: {}", checker.check(&eventually_goal));
    
    // 生成反例
    if let Some(counterexample) = checker.generate_counterexample(&always_safe) {
        println!("   反例: {:?}", counterexample);
    }
    println!();

    // 3. 进程代数示例
    println!("3. 进程代数");
    let interpreter = ProcessAlgebraInterpreter::new();
    
    // 定义进程
    let process_a = ProcessTerm::prefix("a".to_string(), ProcessTerm::nil());
    let process_b = ProcessTerm::prefix("b".to_string(), ProcessTerm::nil());
    let process_c = ProcessTerm::choice(process_a.clone(), process_b.clone());
    let process_d = ProcessTerm::parallel(process_a.clone(), process_b.clone());
    let process_e = ProcessTerm::sequence(process_a.clone(), process_b.clone());
    
    println!("   进程 A: {}", process_a);
    println!("   进程 B: {}", process_b);
    println!("   进程 C (选择): {}", process_c);
    println!("   进程 D (并行): {}", process_d);
    println!("   进程 E (顺序): {}", process_e);
    
    // 执行进程
    let trace_c = interpreter.execute(&process_c);
    let trace_d = interpreter.execute(&process_d);
    let trace_e = interpreter.execute(&process_e);
    
    println!("   进程 C 执行轨迹: {:?}", trace_c);
    println!("   进程 D 执行轨迹: {:?}", trace_d);
    println!("   进程 E 执行轨迹: {:?}", trace_e);
    
    // 检查等价性
    let equivalent = interpreter.are_equivalent(&process_a, &process_b);
    println!("   进程 A 和 B 等价: {}", equivalent);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_finite_state_machine() {
        let mut fsm = FiniteStateMachine::new("start".to_string());
        fsm.add_state(State::new("start".to_string()));
        fsm.add_state(State::new("end".to_string()));
        fsm.add_transition(Transition::new("start".to_string(), "end".to_string(), "go".to_string()));
        
        assert_eq!(fsm.current_state, "start");
        assert!(fsm.can_transition("go"));
        assert!(fsm.transition("go").is_ok());
        assert_eq!(fsm.current_state, "end");
    }

    #[test]
    fn test_temporal_formula() {
        let formula = TemporalFormula::and(
            TemporalFormula::atomic("p".to_string()),
            TemporalFormula::eventually(TemporalFormula::atomic("q".to_string()))
        );
        
        assert_eq!(format!("{}", formula), "(p) ∧ (F(q))");
    }

    #[test]
    fn test_process_term() {
        let process = ProcessTerm::prefix("a".to_string(), ProcessTerm::nil());
        assert_eq!(format!("{}", process), "a.0");
        
        let choice = ProcessTerm::choice(process.clone(), process.clone());
        assert_eq!(format!("{}", choice), "(a.0) + (a.0)");
    }

    #[test]
    fn test_process_algebra_interpreter() {
        let interpreter = ProcessAlgebraInterpreter::new();
        let process = ProcessTerm::prefix("a".to_string(), ProcessTerm::nil());
        
        let trace = interpreter.execute(&process);
        assert_eq!(trace, vec!["a"]);
    }
}
