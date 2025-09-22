//! 领域特定语言(DSL)实现
//! 
//! 本模块实现了各种领域特定语言在Rust中的应用，
//! 包括嵌入式DSL、查询构建器、状态机DSL等。

use std::collections::HashMap;
use std::fmt;
use serde::{Deserialize, Serialize};

/// 嵌入式DSL
pub mod embedded_dsl {

    /// 表达式DSL
    pub trait Expression {
        fn evaluate(&self) -> f64;
    }

    /// 数字表达式
    pub struct Number(f64);

    impl Number {
        pub fn new(value: f64) -> Self {
            Self(value)
        }
    }

    impl Expression for Number {
        fn evaluate(&self) -> f64 {
            self.0
        }
    }

    /// 加法表达式
    pub struct Add {
        left: Box<dyn Expression>,
        right: Box<dyn Expression>,
    }

    impl Add {
        pub fn new(left: Box<dyn Expression>, right: Box<dyn Expression>) -> Self {
            Self { left, right }
        }
    }

    impl Expression for Add {
        fn evaluate(&self) -> f64 {
            self.left.evaluate() + self.right.evaluate()
        }
    }

    /// 乘法表达式
    pub struct Multiply {
        left: Box<dyn Expression>,
        right: Box<dyn Expression>,
    }

    impl Multiply {
        pub fn new(left: Box<dyn Expression>, right: Box<dyn Expression>) -> Self {
            Self { left, right }
        }
    }

    impl Expression for Multiply {
        fn evaluate(&self) -> f64 {
            self.left.evaluate() * self.right.evaluate()
        }
    }

    /// 变量表达式
    #[allow(unused)]
    pub struct Variable {
        name: String,
        value: f64,
    }

    impl Variable {
        pub fn new(name: String, value: f64) -> Self {
            Self { name, value }
        }
    }

    impl Expression for Variable {
        fn evaluate(&self) -> f64 {
            self.value
        }
    }

    /// 表达式构建器
    pub struct ExpressionBuilder;

    impl ExpressionBuilder {
        pub fn number(value: f64) -> Box<dyn Expression> {
            Box::new(Number::new(value))
        }

        pub fn variable(name: String, value: f64) -> Box<dyn Expression> {
            Box::new(Variable::new(name, value))
        }

        pub fn add(left: Box<dyn Expression>, right: Box<dyn Expression>) -> Box<dyn Expression> {
            Box::new(Add::new(left, right))
        }

        pub fn multiply(left: Box<dyn Expression>, right: Box<dyn Expression>) -> Box<dyn Expression> {
            Box::new(Multiply::new(left, right))
        }
    }
}

/// 查询构建器DSL
pub mod query_builder {
    use super::*;

    /// 表
    pub struct Table {
        name: String,
        columns: Vec<Column>,
    }

    impl Table {
        pub fn new(name: String) -> Self {
            Self {
                name,
                columns: Vec::new(),
            }
        }

        pub fn add_column(&mut self, column: Column) {
            self.columns.push(column);
        }

        pub fn get_name(&self) -> &str {
            &self.name
        }

        pub fn get_columns(&self) -> &[Column] {
            &self.columns
        }
    }

    /// 列
    pub struct Column {
        name: String,
        data_type: String,
    }

    impl Column {
        pub fn new(name: String, data_type: String) -> Self {
            Self { name, data_type }
        }

        pub fn get_name(&self) -> &str {
            &self.name
        }

        pub fn get_data_type(&self) -> &str {
            &self.data_type
        }
    }

    /// 查询
    pub struct Query {
        table: String,
        columns: Vec<String>,
        conditions: Vec<Condition>,
        joins: Vec<Join>,
        order_by: Vec<String>,
        limit: Option<u32>,
    }

    impl Query {
        pub fn new(table: String) -> Self {
            Self {
                table,
                columns: Vec::new(),
                conditions: Vec::new(),
                joins: Vec::new(),
                order_by: Vec::new(),
                limit: None,
            }
        }

        pub fn select(mut self, columns: Vec<String>) -> Self {
            self.columns = columns;
            self
        }

        pub fn where_clause(mut self, condition: Condition) -> Self {
            self.conditions.push(condition);
            self
        }

        pub fn join(mut self, join: Join) -> Self {
            self.joins.push(join);
            self
        }

        pub fn order_by(mut self, columns: Vec<String>) -> Self {
            self.order_by = columns;
            self
        }

        pub fn limit(mut self, limit: u32) -> Self {
            self.limit = Some(limit);
            self
        }

        pub fn to_sql(&self) -> String {
            let mut sql = String::new();
            
            // SELECT
            sql.push_str("SELECT ");
            if self.columns.is_empty() {
                sql.push_str("*");
            } else {
                sql.push_str(&self.columns.join(", "));
            }
            
            // FROM
            sql.push_str(&format!(" FROM {}", self.table));
            
            // JOIN
            for join in &self.joins {
                sql.push_str(&format!(" {} JOIN {} ON {}", 
                    join.join_type, join.table, join.condition));
            }
            
            // WHERE
            if !self.conditions.is_empty() {
                sql.push_str(" WHERE ");
                let conditions: Vec<String> = self.conditions
                    .iter()
                    .map(|c| c.to_string())
                    .collect();
                sql.push_str(&conditions.join(" AND "));
            }
            
            // ORDER BY
            if !self.order_by.is_empty() {
                sql.push_str(&format!(" ORDER BY {}", self.order_by.join(", ")));
            }
            
            // LIMIT
            if let Some(limit) = self.limit {
                sql.push_str(&format!(" LIMIT {}", limit));
            }
            
            sql
        }
    }

    /// 条件
    pub struct Condition {
        column: String,
        operator: String,
        value: String,
    }

    impl Condition {
        pub fn new(column: String, operator: String, value: String) -> Self {
            Self { column, operator, value }
        }
    }

    impl fmt::Display for Condition {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{} {} {}", self.column, self.operator, self.value)
        }
    }

    /// 连接
    pub struct Join {
        join_type: String,
        table: String,
        condition: String,
    }

    impl Join {
        pub fn new(join_type: String, table: String, condition: String) -> Self {
            Self { join_type, table, condition }
        }
    }

    /// 查询构建器
    pub struct QueryBuilder;

    impl QueryBuilder {
        pub fn select_from(table: String) -> Query {
            Query::new(table)
        }

        pub fn create_table(name: String) -> Table {
            Table::new(name)
        }

        pub fn create_column(name: String, data_type: String) -> Column {
            Column::new(name, data_type)
        }

        pub fn create_condition(column: String, operator: String, value: String) -> Condition {
            Condition::new(column, operator, value)
        }

        pub fn create_join(join_type: String, table: String, condition: String) -> Join {
            Join::new(join_type, table, condition)
        }
    }
}

/// 状态机DSL
pub mod state_machine_dsl {
    use super::*;

    /// 状态
    #[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
    pub struct State {
        name: String,
        description: Option<String>,
    }

    impl State {
        pub fn new(name: String) -> Self {
            Self { name, description: None }
        }

        pub fn with_description(mut self, description: String) -> Self {
            self.description = Some(description);
            self
        }

        pub fn get_name(&self) -> &str {
            &self.name
        }
    }

    /// 事件
    #[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
    pub struct Event {
        name: String,
        description: Option<String>,
    }

    impl Event {
        pub fn new(name: String) -> Self {
            Self { name, description: None }
        }

        pub fn with_description(mut self, description: String) -> Self {
            self.description = Some(description);
            self
        }

        pub fn get_name(&self) -> &str {
            &self.name
        }
    }

    /// 转换
    #[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
    pub struct Transition {
        from_state: State,
        event: Event,
        to_state: State,
        action: Option<String>,
    }

    impl Transition {
        pub fn new(from_state: State, event: Event, to_state: State) -> Self {
            Self {
                from_state,
                event,
                to_state,
                action: None,
            }
        }

        pub fn with_action(mut self, action: String) -> Self {
            self.action = Some(action);
            self
        }

        pub fn get_from_state(&self) -> &State {
            &self.from_state
        }

        pub fn get_event(&self) -> &Event {
            &self.event
        }

        pub fn get_to_state(&self) -> &State {
            &self.to_state
        }
    }

    /// 状态机
    pub struct StateMachine {
        name: String,
        states: Vec<State>,
        events: Vec<Event>,
        transitions: Vec<Transition>,
        initial_state: Option<State>,
        current_state: Option<State>,
    }

    impl StateMachine {
        pub fn new(name: String) -> Self {
            Self {
                name,
                states: Vec::new(),
                events: Vec::new(),
                transitions: Vec::new(),
                initial_state: None,
                current_state: None,
            }
        }

        pub fn add_state(mut self, state: State) -> Self {
            self.states.push(state);
            self
        }

        pub fn add_event(mut self, event: Event) -> Self {
            self.events.push(event);
            self
        }

        pub fn add_transition(mut self, transition: Transition) -> Self {
            self.transitions.push(transition);
            self
        }

        pub fn set_initial_state(mut self, state: State) -> Self {
            self.initial_state = Some(state.clone());
            self.current_state = Some(state);
            self
        }

        pub fn process_event(&mut self, event: &Event) -> Result<(), String> {
            if let Some(current_state) = &self.current_state {
                for transition in &self.transitions {
                    if transition.get_from_state() == current_state && transition.get_event() == event {
                        self.current_state = Some(transition.get_to_state().clone());
                        if let Some(action) = &transition.action {
                            println!("Executing action: {}", action);
                        }
                        return Ok(());
                    }
                }
                Err(format!("No transition found from state {:?} for event {:?}", current_state, event))
            } else {
                Err("No current state set".to_string())
            }
        }

        pub fn get_current_state(&self) -> Option<&State> {
            self.current_state.as_ref()
        }

        pub fn get_name(&self) -> &str {
            &self.name
        }
    }

    /// 状态机构建器
    pub struct StateMachineBuilder;

    impl StateMachineBuilder {
        pub fn create_state(name: String) -> State {
            State::new(name)
        }

        pub fn create_event(name: String) -> Event {
            Event::new(name)
        }

        pub fn create_transition(from_state: State, event: Event, to_state: State) -> Transition {
            Transition::new(from_state, event, to_state)
        }

        pub fn create_state_machine(name: String) -> StateMachine {
            StateMachine::new(name)
        }
    }
}

/// 配置DSL
pub mod config_dsl {
    use super::*;

    /// 配置值
    #[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
    pub enum ConfigValue {
        String(String),
        Integer(i64),
        Float(f64),
        Boolean(bool),
        List(Vec<ConfigValue>),
        Map(HashMap<String, ConfigValue>),
    }

    /// 配置
    pub struct Config {
        values: HashMap<String, ConfigValue>,
    }

    impl Config {
        pub fn new() -> Self {
            Self {
                values: HashMap::new(),
            }
        }

        pub fn set(&mut self, key: String, value: ConfigValue) {
            self.values.insert(key, value);
        }

        pub fn get(&self, key: &str) -> Option<&ConfigValue> {
            self.values.get(key)
        }

        pub fn get_string(&self, key: &str) -> Option<&String> {
            if let Some(ConfigValue::String(value)) = self.get(key) {
                Some(value)
            } else {
                None
            }
        }

        pub fn get_integer(&self, key: &str) -> Option<i64> {
            if let Some(ConfigValue::Integer(value)) = self.get(key) {
                Some(*value)
            } else {
                None
            }
        }

        pub fn get_float(&self, key: &str) -> Option<f64> {
            if let Some(ConfigValue::Float(value)) = self.get(key) {
                Some(*value)
            } else {
                None
            }
        }

        pub fn get_boolean(&self, key: &str) -> Option<bool> {
            if let Some(ConfigValue::Boolean(value)) = self.get(key) {
                Some(*value)
            } else {
                None
            }
        }
    }

    /// 配置构建器
    pub struct ConfigBuilder {
        config: Config,
    }

    impl ConfigBuilder {
        pub fn new() -> Self {
            Self {
                config: Config::new(),
            }
        }

        pub fn string(mut self, key: String, value: String) -> Self {
            self.config.set(key, ConfigValue::String(value));
            self
        }

        pub fn integer(mut self, key: String, value: i64) -> Self {
            self.config.set(key, ConfigValue::Integer(value));
            self
        }

        pub fn float(mut self, key: String, value: f64) -> Self {
            self.config.set(key, ConfigValue::Float(value));
            self
        }

        pub fn boolean(mut self, key: String, value: bool) -> Self {
            self.config.set(key, ConfigValue::Boolean(value));
            self
        }

        pub fn list(mut self, key: String, value: Vec<ConfigValue>) -> Self {
            self.config.set(key, ConfigValue::List(value));
            self
        }

        pub fn map(mut self, key: String, value: HashMap<String, ConfigValue>) -> Self {
            self.config.set(key, ConfigValue::Map(value));
            self
        }

        pub fn build(self) -> Config {
            self.config
        }
    }
}

/// DSL工具集
pub mod dsl_toolkit {
    use super::*;

    /// DSL工具集
    pub struct DSLToolkit {
        pub expression_builder: embedded_dsl::ExpressionBuilder,
        pub query_builder: query_builder::QueryBuilder,
        pub state_machine_builder: state_machine_dsl::StateMachineBuilder,
    }

    impl DSLToolkit {
        pub fn new() -> Self {
            Self {
                expression_builder: embedded_dsl::ExpressionBuilder,
                query_builder: query_builder::QueryBuilder,
                state_machine_builder: state_machine_dsl::StateMachineBuilder,
            }
        }

        /// 创建复杂表达式
        pub fn create_complex_expression(&self) -> Box<dyn embedded_dsl::Expression> {
            let x = embedded_dsl::ExpressionBuilder::variable("x".to_string(), 5.0);
            let y = embedded_dsl::ExpressionBuilder::variable("y".to_string(), 3.0);
            let sum = embedded_dsl::ExpressionBuilder::add(x, y);
            let product = embedded_dsl::ExpressionBuilder::multiply(sum, embedded_dsl::ExpressionBuilder::number(2.0));
            product
        }

        /// 创建复杂查询
        pub fn create_complex_query(&self) -> query_builder::Query {
            query_builder::QueryBuilder::select_from("users".to_string())
                .select(vec!["id".to_string(), "name".to_string(), "email".to_string()])
                .where_clause(query_builder::QueryBuilder::create_condition(
                    "age".to_string(),
                    ">=".to_string(),
                    "18".to_string(),
                ))
                .join(query_builder::QueryBuilder::create_join(
                    "INNER".to_string(),
                    "orders".to_string(),
                    "users.id = orders.user_id".to_string(),
                ))
                .order_by(vec!["name".to_string()])
                .limit(10)
        }

        /// 创建状态机
        pub fn create_state_machine(&self) -> state_machine_dsl::StateMachine {
            let idle = state_machine_dsl::StateMachineBuilder::create_state("idle".to_string());
            let running = state_machine_dsl::StateMachineBuilder::create_state("running".to_string());
            let stopped = state_machine_dsl::StateMachineBuilder::create_state("stopped".to_string());

            let start = state_machine_dsl::StateMachineBuilder::create_event("start".to_string());
            let stop = state_machine_dsl::StateMachineBuilder::create_event("stop".to_string());

            let transition1 = state_machine_dsl::StateMachineBuilder::create_transition(
                idle.clone(),
                start.clone(),
                running.clone(),
            ).with_action("Starting the process".to_string());

            let transition2 = state_machine_dsl::StateMachineBuilder::create_transition(
                running.clone(),
                stop.clone(),
                stopped.clone(),
            ).with_action("Stopping the process".to_string());

            state_machine_dsl::StateMachineBuilder::create_state_machine("ProcessStateMachine".to_string())
                .add_state(idle.clone())
                .add_state(running)
                .add_state(stopped)
                .add_event(start)
                .add_event(stop)
                .add_transition(transition1)
                .add_transition(transition2)
                .set_initial_state(idle)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expression_dsl() {
        let x = embedded_dsl::ExpressionBuilder::variable("x".to_string(), 5.0);
        let y = embedded_dsl::ExpressionBuilder::variable("y".to_string(), 3.0);
        let sum = embedded_dsl::ExpressionBuilder::add(x, y);
        let product = embedded_dsl::ExpressionBuilder::multiply(sum, embedded_dsl::ExpressionBuilder::number(2.0));
        
        assert_eq!(product.evaluate(), 16.0);
    }

    #[test]
    fn test_query_builder_dsl() {
        let query = query_builder::QueryBuilder::select_from("users".to_string())
            .select(vec!["id".to_string(), "name".to_string()])
            .where_clause(query_builder::QueryBuilder::create_condition(
                "age".to_string(),
                ">=".to_string(),
                "18".to_string(),
            ))
            .limit(10);

        let sql = query.to_sql();
        assert!(sql.contains("SELECT id, name"));
        assert!(sql.contains("FROM users"));
        assert!(sql.contains("WHERE age >= 18"));
        assert!(sql.contains("LIMIT 10"));
    }

    #[test]
    fn test_state_machine_dsl() {
        let idle = state_machine_dsl::StateMachineBuilder::create_state("idle".to_string());
        let running = state_machine_dsl::StateMachineBuilder::create_state("running".to_string());
        let start = state_machine_dsl::StateMachineBuilder::create_event("start".to_string());

        let mut state_machine = state_machine_dsl::StateMachineBuilder::create_state_machine("TestSM".to_string())
            .add_state(idle.clone())
            .add_state(running.clone())
            .add_event(start.clone())
            .add_transition(state_machine_dsl::StateMachineBuilder::create_transition(
                idle.clone(),
                start,
                running.clone(),
            ))
            .set_initial_state(idle);

        assert_eq!(state_machine.get_current_state().unwrap().get_name(), "idle");

        let start_event = state_machine_dsl::StateMachineBuilder::create_event("start".to_string());
        state_machine.process_event(&start_event).unwrap();
        assert_eq!(state_machine.get_current_state().unwrap().get_name(), "running");
    }

    #[test]
    fn test_config_dsl() {
        let config = config_dsl::ConfigBuilder::new()
            .string("name".to_string(), "test".to_string())
            .integer("port".to_string(), 8080)
            .float("timeout".to_string(), 30.5)
            .boolean("debug".to_string(), true)
            .build();

        assert_eq!(config.get_string("name"), Some(&"test".to_string()));
        assert_eq!(config.get_integer("port"), Some(8080));
        assert_eq!(config.get_float("timeout"), Some(30.5));
        assert_eq!(config.get_boolean("debug"), Some(true));
    }

    #[test]
    fn test_dsl_toolkit() {
        let toolkit = dsl_toolkit::DSLToolkit::new();
        
        let expression = toolkit.create_complex_expression();
        assert_eq!(expression.evaluate(), 16.0);
        
        let query = toolkit.create_complex_query();
        let sql = query.to_sql();
        assert!(sql.contains("SELECT id, name, email"));
        
        let state_machine = toolkit.create_state_machine();
        assert_eq!(state_machine.get_name(), "ProcessStateMachine");
    }
}
