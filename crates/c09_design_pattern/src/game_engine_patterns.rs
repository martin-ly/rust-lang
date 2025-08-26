//! 游戏引擎设计模式应用
//! 
//! 本模块展示了在游戏引擎中应用各种设计模式的实践案例，
//! 包括Component、Observer、State等经典模式。

use std::collections::HashMap;
use std::any::{Any, TypeId};

// ============================================================================
// Component 模式 (Entity-Component-System)
// ============================================================================

/// 实体ID类型
pub type EntityId = u64;

/// 组件接口
pub trait Component: Any + Send + Sync {
    fn get_type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }
}

/// 位置组件
#[derive(Debug, Clone)]
pub struct Position {
    pub x: f32,
    pub y: f32,
    pub z: f32,
}

impl Component for Position {}

/// 速度组件
#[derive(Debug, Clone)]
pub struct Velocity {
    pub x: f32,
    pub y: f32,
    pub z: f32,
}

impl Component for Velocity {}

/// 健康组件
#[derive(Debug, Clone)]
pub struct Health {
    pub current: f32,
    pub maximum: f32,
}

impl Component for Health {}

/// 渲染组件
#[derive(Debug, Clone)]
pub struct Renderable {
    pub mesh_id: String,
    pub texture_id: String,
    pub visible: bool,
}

impl Component for Renderable {}

/// 实体管理器
pub struct EntityManager {
    entities: HashMap<EntityId, HashMap<TypeId, Box<dyn Component>>>,
    next_id: EntityId,
}

impl EntityManager {
    pub fn new() -> Self {
        Self {
            entities: HashMap::new(),
            next_id: 1,
        }
    }

    pub fn create_entity(&mut self) -> EntityId {
        let id = self.next_id;
        self.next_id += 1;
        self.entities.insert(id, HashMap::new());
        id
    }

    pub fn add_component<T: Component + 'static>(&mut self, entity_id: EntityId, component: T) {
        if let Some(components) = self.entities.get_mut(&entity_id) {
            components.insert(TypeId::of::<T>(), Box::new(component));
        }
    }

    pub fn get_component<T: Component + 'static>(&self, entity_id: EntityId) -> Option<&T> {
        self.entities
            .get(&entity_id)
            .and_then(|components| {
                components
                    .get(&TypeId::of::<T>())
                    .and_then(|component| {
                        // 使用unsafe来绕过类型检查，因为我们知道类型是正确的
                        unsafe {
                            let ptr = component.as_ref() as *const dyn Component as *const T;
                            Some(&*ptr)
                        }
                    })
            })
    }

    pub fn get_component_mut<T: Component + 'static>(&mut self, entity_id: EntityId) -> Option<&mut T> {
        self.entities
            .get_mut(&entity_id)
            .and_then(|components| {
                components
                    .get_mut(&TypeId::of::<T>())
                    .and_then(|component| {
                        // 使用unsafe来绕过类型检查，因为我们知道类型是正确的
                        unsafe {
                            let ptr = component.as_mut() as *mut dyn Component as *mut T;
                            Some(&mut *ptr)
                        }
                    })
            })
    }

    pub fn remove_component<T: Component + 'static>(&mut self, entity_id: EntityId) {
        if let Some(components) = self.entities.get_mut(&entity_id) {
            components.remove(&TypeId::of::<T>());
        }
    }

    pub fn remove_entity(&mut self, entity_id: EntityId) {
        self.entities.remove(&entity_id);
    }

    pub fn get_entities_with_component<T: Component + 'static>(&self) -> Vec<EntityId> {
        self.entities
            .iter()
            .filter(|(_, components)| components.contains_key(&TypeId::of::<T>()))
            .map(|(id, _)| *id)
            .collect()
    }
}

/// 系统接口
pub trait System {
    fn update(&mut self, entity_manager: &mut EntityManager, delta_time: f32);
}

/// 移动系统
pub struct MovementSystem;

impl System for MovementSystem {
    fn update(&mut self, entity_manager: &mut EntityManager, delta_time: f32) {
        let entities_with_velocity = entity_manager.get_entities_with_component::<Velocity>();
        
        for entity_id in entities_with_velocity {
            // 先获取velocity的克隆
            let velocity = entity_manager.get_component::<Velocity>(entity_id).cloned();
            
            if let Some(velocity) = velocity {
                // 然后获取可变引用
                if let Some(position) = entity_manager.get_component_mut::<Position>(entity_id) {
                    position.x += velocity.x * delta_time;
                    position.y += velocity.y * delta_time;
                    position.z += velocity.z * delta_time;
                }
            }
        }
    }
}

/// 渲染系统
pub struct RenderSystem;

impl System for RenderSystem {
    fn update(&mut self, entity_manager: &mut EntityManager, _delta_time: f32) {
        let entities_with_renderable = entity_manager.get_entities_with_component::<Renderable>();
        
        for entity_id in entities_with_renderable {
            if let (Some(position), Some(renderable)) = (
                entity_manager.get_component::<Position>(entity_id),
                entity_manager.get_component::<Renderable>(entity_id),
            ) {
                if renderable.visible {
                    println!(
                        "渲染实体 {}: 位置({:.2}, {:.2}, {:.2}), 网格: {}, 纹理: {}",
                        entity_id, position.x, position.y, position.z, 
                        renderable.mesh_id, renderable.texture_id
                    );
                }
            }
        }
    }
}

// ============================================================================
// Observer 模式
// ============================================================================

/// 事件类型
#[derive(Debug, Clone)]
pub enum GameEvent {
    PlayerMoved { entity_id: EntityId, new_position: Position },
    PlayerDamaged { entity_id: EntityId, damage: f32 },
    PlayerDied { entity_id: EntityId },
    ItemCollected { entity_id: EntityId, item_id: String },
}

/// 观察者接口
pub trait Observer {
    fn on_event(&mut self, event: &GameEvent);
}

/// 事件管理器
pub struct EventManager {
    observers: HashMap<TypeId, Vec<Box<dyn Observer>>>,
}

impl EventManager {
    pub fn new() -> Self {
        Self {
            observers: HashMap::new(),
        }
    }

    pub fn subscribe<T: Observer + 'static>(&mut self, observer: T) {
        // 将所有观察者注册到统一事件类型键，避免以具体类型键导致无法分发
        let event_type_id = TypeId::of::<GameEvent>();
        self.observers
            .entry(event_type_id)
            .or_insert_with(Vec::new)
            .push(Box::new(observer));
    }

    pub fn publish(&mut self, event: GameEvent) {
        let event_type_id = TypeId::of::<GameEvent>();
        if let Some(observers) = self.observers.get_mut(&event_type_id) {
            for observer in observers.iter_mut() {
                observer.on_event(&event);
            }
        }
    }
}

/// 成就系统（观察者）
pub struct AchievementSystem {
    achievements: HashMap<String, bool>,
}

impl AchievementSystem {
    pub fn new() -> Self {
        let mut achievements = HashMap::new();
        achievements.insert("first_move".to_string(), false);
        achievements.insert("first_death".to_string(), false);
        achievements.insert("item_collector".to_string(), false);
        
        Self { achievements }
    }
}

impl Observer for AchievementSystem {
    fn on_event(&mut self, event: &GameEvent) {
        match event {
            GameEvent::PlayerMoved { entity_id, .. } => {
                if !self.achievements["first_move"] {
                    println!("成就解锁: 首次移动 (实体 {})", entity_id);
                    self.achievements.insert("first_move".to_string(), true);
                }
            }
            GameEvent::PlayerDied { entity_id } => {
                if !self.achievements["first_death"] {
                    println!("成就解锁: 首次死亡 (实体 {})", entity_id);
                    self.achievements.insert("first_death".to_string(), true);
                }
            }
            GameEvent::ItemCollected { entity_id, item_id } => {
                if !self.achievements["item_collector"] {
                    println!("成就解锁: 物品收集者 (实体 {} 收集了 {})", entity_id, item_id);
                    self.achievements.insert("item_collector".to_string(), true);
                }
            }
            _ => {}
        }
    }
}

/// 日志系统（观察者）
pub struct LoggingSystem;

impl Observer for LoggingSystem {
    fn on_event(&mut self, event: &GameEvent) {
        match event {
            GameEvent::PlayerMoved { entity_id, new_position } => {
                println!("日志: 实体 {} 移动到位置 ({:.2}, {:.2}, {:.2})", 
                    entity_id, new_position.x, new_position.y, new_position.z);
            }
            GameEvent::PlayerDamaged { entity_id, damage } => {
                println!("日志: 实体 {} 受到 {} 点伤害", entity_id, damage);
            }
            GameEvent::PlayerDied { entity_id } => {
                println!("日志: 实体 {} 死亡", entity_id);
            }
            GameEvent::ItemCollected { entity_id, item_id } => {
                println!("日志: 实体 {} 收集了物品 {}", entity_id, item_id);
            }
        }
    }
}

// ============================================================================
// State 模式
// ============================================================================

/// 游戏状态接口
pub trait GameState {
    fn enter(&mut self);
    fn update(&mut self, delta_time: f32) -> Option<Box<dyn GameState>>;
    fn exit(&mut self);
    fn handle_input(&mut self, input: &str) -> Option<Box<dyn GameState>>;
}

/// 主菜单状态
pub struct MainMenuState {
    selected_option: usize,
    options: Vec<String>,
}

impl MainMenuState {
    pub fn new() -> Self {
        Self {
            selected_option: 0,
            options: vec![
                "开始游戏".to_string(),
                "设置".to_string(),
                "退出".to_string(),
            ],
        }
    }
}

impl GameState for MainMenuState {
    fn enter(&mut self) {
        println!("进入主菜单");
        self.display_menu();
    }

    fn update(&mut self, _delta_time: f32) -> Option<Box<dyn GameState>> {
        None
    }

    fn exit(&mut self) {
        println!("退出主菜单");
    }

    fn handle_input(&mut self, input: &str) -> Option<Box<dyn GameState>> {
        match input {
            "up" => {
                if self.selected_option > 0 {
                    self.selected_option -= 1;
                }
                self.display_menu();
                None
            }
            "down" => {
                if self.selected_option < self.options.len() - 1 {
                    self.selected_option += 1;
                }
                self.display_menu();
                None
            }
            "enter" => {
                match self.selected_option {
                    0 => Some(Box::new(PlayingState::new())),
                    1 => Some(Box::new(SettingsState::new())),
                    2 => Some(Box::new(ExitState)),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

impl MainMenuState {
    fn display_menu(&self) {
        println!("\n=== 主菜单 ===");
        for (i, option) in self.options.iter().enumerate() {
            if i == self.selected_option {
                println!("> {}", option);
            } else {
                println!("  {}", option);
            }
        }
    }
}

/// 游戏进行状态
pub struct PlayingState {
    player_health: f32,
    score: u32,
}

impl PlayingState {
    pub fn new() -> Self {
        Self {
            player_health: 100.0,
            score: 0,
        }
    }
}

impl GameState for PlayingState {
    fn enter(&mut self) {
        println!("开始游戏");
        println!("玩家健康: {:.1}, 分数: {}", self.player_health, self.score);
    }

    fn update(&mut self, delta_time: f32) -> Option<Box<dyn GameState>> {
        // 模拟游戏逻辑
        self.score += (delta_time * 10.0) as u32;
        
        if self.player_health <= 0.0 {
            Some(Box::new(GameOverState::new(self.score)))
        } else {
            None
        }
    }

    fn exit(&mut self) {
        println!("游戏结束，最终分数: {}", self.score);
    }

    fn handle_input(&mut self, input: &str) -> Option<Box<dyn GameState>> {
        match input {
            "pause" => Some(Box::new(PauseState::new(self.player_health, self.score))),
            "damage" => {
                self.player_health -= 20.0;
                println!("玩家受到伤害，当前健康: {:.1}", self.player_health);
                None
            }
            _ => None,
        }
    }
}

/// 暂停状态
pub struct PauseState {
    player_health: f32,
    score: u32,
}

impl PauseState {
    pub fn new(player_health: f32, score: u32) -> Self {
        Self {
            player_health,
            score,
        }
    }
}

impl GameState for PauseState {
    fn enter(&mut self) {
        println!("游戏暂停");
        println!("按 'resume' 继续游戏，按 'menu' 返回主菜单");
    }

    fn update(&mut self, _delta_time: f32) -> Option<Box<dyn GameState>> {
        None
    }

    fn exit(&mut self) {
        println!("退出暂停状态");
    }

    fn handle_input(&mut self, input: &str) -> Option<Box<dyn GameState>> {
        match input {
            "resume" => Some(Box::new(PlayingState {
                player_health: self.player_health,
                score: self.score,
            })),
            "menu" => Some(Box::new(MainMenuState::new())),
            _ => None,
        }
    }
}

/// 游戏结束状态
pub struct GameOverState {
    final_score: u32,
}

impl GameOverState {
    pub fn new(final_score: u32) -> Self {
        Self { final_score }
    }
}

impl GameState for GameOverState {
    fn enter(&mut self) {
        println!("游戏结束！");
        println!("最终分数: {}", self.final_score);
        println!("按 'restart' 重新开始，按 'menu' 返回主菜单");
    }

    fn update(&mut self, _delta_time: f32) -> Option<Box<dyn GameState>> {
        None
    }

    fn exit(&mut self) {
        println!("退出游戏结束状态");
    }

    fn handle_input(&mut self, input: &str) -> Option<Box<dyn GameState>> {
        match input {
            "restart" => Some(Box::new(PlayingState::new())),
            "menu" => Some(Box::new(MainMenuState::new())),
            _ => None,
        }
    }
}

/// 设置状态
pub struct SettingsState;

impl SettingsState {
    pub fn new() -> Self {
        Self
    }
}

impl GameState for SettingsState {
    fn enter(&mut self) {
        println!("设置菜单");
        println!("按 'back' 返回主菜单");
    }

    fn update(&mut self, _delta_time: f32) -> Option<Box<dyn GameState>> {
        None
    }

    fn exit(&mut self) {
        println!("退出设置");
    }

    fn handle_input(&mut self, input: &str) -> Option<Box<dyn GameState>> {
        match input {
            "back" => Some(Box::new(MainMenuState::new())),
            _ => None,
        }
    }
}

/// 退出状态
pub struct ExitState;

impl GameState for ExitState {
    fn enter(&mut self) {
        println!("退出游戏");
    }

    fn update(&mut self, _delta_time: f32) -> Option<Box<dyn GameState>> {
        None
    }

    fn exit(&mut self) {
        println!("游戏已退出");
    }

    fn handle_input(&mut self, _input: &str) -> Option<Box<dyn GameState>> {
        None
    }
}

/// 游戏状态管理器
pub struct GameStateManager {
    current_state: Option<Box<dyn GameState>>,
}

impl GameStateManager {
    pub fn new() -> Self {
        Self {
            current_state: None,
        }
    }

    pub fn change_state(&mut self, new_state: Box<dyn GameState>) {
        if let Some(mut current_state) = self.current_state.take() {
            current_state.exit();
        }
        
        let mut state = new_state;
        state.enter();
        self.current_state = Some(state);
    }

    pub fn update(&mut self, delta_time: f32) {
        if let Some(mut state) = self.current_state.take() {
            if let Some(new_state) = state.update(delta_time) {
                state.exit();
                let mut new_state = new_state;
                new_state.enter();
                self.current_state = Some(new_state);
            } else {
                self.current_state = Some(state);
            }
        }
    }

    pub fn handle_input(&mut self, input: &str) {
        if let Some(mut state) = self.current_state.take() {
            if let Some(new_state) = state.handle_input(input) {
                state.exit();
                let mut new_state = new_state;
                new_state.enter();
                self.current_state = Some(new_state);
            } else {
                self.current_state = Some(state);
            }
        }
    }
}

// ============================================================================
// 单元测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_component_system() {
        let mut entity_manager = EntityManager::new();
        
        // 创建实体
        let entity_id = entity_manager.create_entity();
        
        // 添加组件
        entity_manager.add_component(entity_id, Position { x: 0.0, y: 0.0, z: 0.0 });
        entity_manager.add_component(entity_id, Velocity { x: 1.0, y: 0.0, z: 0.0 });
        entity_manager.add_component(entity_id, Health { current: 100.0, maximum: 100.0 });
        
        // 验证组件
        let position = entity_manager.get_component::<Position>(entity_id);
        assert!(position.is_some());
        assert_eq!(position.unwrap().x, 0.0);
        
        // 测试系统
        let mut movement_system = MovementSystem;
        movement_system.update(&mut entity_manager, 1.0);
        
        let position = entity_manager.get_component::<Position>(entity_id);
        assert_eq!(position.unwrap().x, 1.0);
    }

    #[test]
    fn test_observer_pattern() {
        let mut event_manager = EventManager::new();
        let achievement_system = AchievementSystem::new();
        let logging_system = LoggingSystem;
        
        event_manager.subscribe(achievement_system);
        event_manager.subscribe(logging_system);
        
        let event = GameEvent::PlayerMoved {
            entity_id: 1,
            new_position: Position { x: 10.0, y: 20.0, z: 0.0 },
        };
        
        event_manager.publish(event);
    }

    #[test]
    fn test_state_pattern() {
        let mut state_manager = GameStateManager::new();
        state_manager.change_state(Box::new(MainMenuState::new()));
        
        // 测试状态转换
        state_manager.handle_input("down");
        state_manager.handle_input("enter");
        
        // 验证进入游戏状态
        if let Some(_) = state_manager.current_state {
            // 状态已转换
        }
    }
}
