//! 高级并发模式示例
//!
//! 本示例展示了复杂并发场景下的设计模式：
//! - Actor 模型
//! - 发布-订阅模式
//! - 管道模式
//! - 扇出-扇入模式
//! - 背压处理
//! - 熔断器模式
//! - 限流器模式

use std::sync::{Arc, Mutex, atomic::{AtomicUsize, Ordering}};
use std::thread;
use std::time::{Duration, Instant};
use std::collections::HashMap;
use crossbeam_channel::{unbounded, Receiver, Sender};

/// Actor 模型实现
#[allow(dead_code)]
pub struct Actor<Message> {
    receiver: Receiver<Message>,
    sender: Sender<Message>,
    name: String,
    state: Arc<Mutex<ActorState>>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct ActorState {
    message_count: usize,
    last_message_time: Option<Instant>,
}

impl<Message> Actor<Message>
where
    Message: Send + 'static,
{
    pub fn new(name: String, handler: impl Fn(Message, &mut ActorState) + Send + 'static) -> Self {
        let (sender, receiver) = unbounded();
        let state = Arc::new(Mutex::new(ActorState {
            message_count: 0,
            last_message_time: None,
        }));

        let state_clone = Arc::clone(&state);
        let receiver_clone = receiver.clone();
        let name_clone = name.clone();
        
        thread::spawn(move || {
            println!("Actor '{}' 启动", name_clone);
            
            while let Ok(message) = receiver_clone.recv() {
                let mut state = state_clone.lock().unwrap();
                handler(message, &mut state);
            }
            
            println!("Actor '{}' 停止", name_clone);
        });

        Self {
            receiver,
            sender,
            name,
            state,
        }
    }

    pub fn send(&self, message: Message) -> Result<(), crossbeam_channel::SendError<Message>> {
        self.sender.send(message)
    }

    pub fn get_state(&self) -> ActorState {
        self.state.lock().unwrap().clone()
    }

    pub fn shutdown(self) {
        drop(self.sender);
    }
}

/// 发布-订阅模式
#[allow(dead_code)]
pub struct PubSub<T> {
    subscribers: Arc<Mutex<HashMap<String, Sender<T>>>>,
    publisher: Sender<T>,
}

impl<T> PubSub<T>
where
    T: Clone + Send + 'static,
{
    pub fn new() -> Self {
        let (publisher, receiver) = unbounded::<T>();
        let subscribers = Arc::new(Mutex::new(HashMap::<String, Sender<T>>::new()));

        let subscribers_clone = Arc::clone(&subscribers);
        
        thread::spawn(move || {
            while let Ok(message) = receiver.recv() {
                let subs = subscribers_clone.lock().unwrap();
                for (name, sender) in subs.iter() {
                    if let Err(_) = sender.send(message.clone()) {
                        println!("订阅者 '{}' 断开连接", name);
                    }
                }
            }
        });

        Self {
            subscribers,
            publisher,
        }
    }

    pub fn subscribe(&self, name: String) -> Receiver<T> {
        let (sender, receiver) = unbounded();
        self.subscribers.lock().unwrap().insert(name, sender);
        receiver
    }

    pub fn unsubscribe(&self, name: &str) {
        self.subscribers.lock().unwrap().remove(name);
    }

    pub fn publish(&self, message: T) -> Result<(), crossbeam_channel::SendError<T>> {
        self.publisher.send(message)
    }

    pub fn get_subscriber_count(&self) -> usize {
        self.subscribers.lock().unwrap().len()
    }
}

/// 管道模式
#[allow(dead_code)]
pub struct Pipeline {
    input: Sender<String>,
    output: Receiver<String>,
}

impl Pipeline {
    pub fn new() -> Self {
        let (input, receiver) = unbounded();
        let (sender, output) = unbounded();

        // 第一个阶段
        let (sender2, receiver2) = unbounded();
        thread::spawn(move || {
            while let Ok(data) = receiver.recv() {
                let processed = format!("Stage1: {}", data);
                if sender2.send(processed).is_err() {
                    break;
                }
            }
        });

        // 第二个阶段
        let (sender3, receiver3) = unbounded();
        thread::spawn(move || {
            while let Ok(data) = receiver2.recv() {
                let processed = format!("Stage2: {}", data);
                if sender3.send(processed).is_err() {
                    break;
                }
            }
        });

        // 第三个阶段
        thread::spawn(move || {
            while let Ok(data) = receiver3.recv() {
                let processed = format!("Stage3: {}", data);
                if sender.send(processed).is_err() {
                    break;
                }
            }
        });

        Self {
            input,
            output,
        }
    }

    pub fn send(&self, data: String) -> Result<(), crossbeam_channel::SendError<String>> {
        self.input.send(data)
    }

    pub fn recv(&self) -> Result<String, crossbeam_channel::RecvError> {
        self.output.recv()
    }
}

/// 扇出-扇入模式
#[allow(dead_code)]
pub struct FanOutFanIn {
    input: Sender<String>,
    final_output: Receiver<String>,
}

impl FanOutFanIn {
    pub fn new(num_workers: usize) -> Self {
        let (input, receiver) = unbounded();
        let mut worker_outputs = Vec::new();
        let mut worker_receivers = Vec::new();

        // 创建工作者
        for i in 0..num_workers {
            let (sender, worker_receiver) = unbounded();
            let input_receiver = receiver.clone();
            
            let sender_clone = sender.clone();
            worker_outputs.push(sender);
            worker_receivers.push(worker_receiver);

            thread::spawn(move || {
                println!("扇出工作者 {} 启动", i);
                
                while let Ok(data) = input_receiver.recv() {
                    // 模拟处理
                    thread::sleep(Duration::from_millis(10));
                    let processed = format!("Worker-{}: {}", i, data);
                    
                    if sender_clone.send(processed).is_err() {
                        break;
                    }
                }
                
                println!("扇出工作者 {} 停止", i);
            });
        }

        // 聚合器
        let (final_sender, final_output) = unbounded();
        
        thread::spawn(move || {
            println!("扇入聚合器启动");
            
            let mut results = Vec::new();
            let active_workers = num_workers;
            
            while active_workers > 0 {
                for (_i, receiver) in worker_receivers.iter().enumerate() {
                    if let Ok(result) = receiver.try_recv() {
                        results.push(result);
                        
                        if results.len() == num_workers {
                            let aggregated = format!("聚合结果: {:?}", results);
                            if final_sender.send(aggregated).is_err() {
                                break;
                            }
                            results.clear();
                        }
                    }
                }
                thread::sleep(Duration::from_millis(1));
            }
            
            println!("扇入聚合器停止");
        });

        Self {
            input,
            final_output,
        }
    }

    pub fn send(&self, data: String) -> Result<(), crossbeam_channel::SendError<String>> {
        self.input.send(data)
    }

    pub fn recv(&self) -> Result<String, crossbeam_channel::RecvError> {
        self.final_output.recv()
    }
}

/// 熔断器模式
#[allow(dead_code)]
pub struct CircuitBreaker {
    state: Arc<Mutex<CircuitState>>,
    failure_threshold: usize,
    timeout: Duration,
    last_failure_time: Arc<Mutex<Option<Instant>>>,
    failure_count: Arc<AtomicUsize>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum CircuitState {
    Closed,
    Open,
    HalfOpen,
}

impl CircuitBreaker {
    pub fn new(failure_threshold: usize, timeout: Duration) -> Self {
        Self {
            state: Arc::new(Mutex::new(CircuitState::Closed)),
            failure_threshold,
            timeout,
            last_failure_time: Arc::new(Mutex::new(None)),
            failure_count: Arc::new(AtomicUsize::new(0)),
        }
    }

    pub fn call<F, R>(&self, f: F) -> Result<R, String>
    where
        F: FnOnce() -> Result<R, String>,
    {
        let state = self.state.lock().unwrap();
        
        match *state {
            CircuitState::Open => {
                let last_failure = self.last_failure_time.lock().unwrap();
                if let Some(time) = *last_failure {
                    if Instant::now() - time > self.timeout {
                        drop(state);
                        drop(last_failure);
                        self.transition_to_half_open();
                        return self.call(f);
                    }
                }
                Err("熔断器开启".to_string())
            }
            CircuitState::HalfOpen => {
                drop(state);
                match f() {
                    Ok(result) => {
                        self.transition_to_closed();
                        Ok(result)
                    }
                    Err(e) => {
                        self.transition_to_open();
                        Err(e)
                    }
                }
            }
            CircuitState::Closed => {
                drop(state);
                match f() {
                    Ok(result) => {
                        self.failure_count.store(0, Ordering::Relaxed);
                        Ok(result)
                    }
                    Err(e) => {
                        let count = self.failure_count.fetch_add(1, Ordering::Relaxed) + 1;
                        if count >= self.failure_threshold {
                            self.transition_to_open();
                        }
                        Err(e)
                    }
                }
            }
        }
    }

    fn transition_to_open(&self) {
        let mut state = self.state.lock().unwrap();
        *state = CircuitState::Open;
        *self.last_failure_time.lock().unwrap() = Some(Instant::now());
        println!("熔断器状态: Closed -> Open");
    }

    fn transition_to_half_open(&self) {
        let mut state = self.state.lock().unwrap();
        *state = CircuitState::HalfOpen;
        println!("熔断器状态: Open -> HalfOpen");
    }

    fn transition_to_closed(&self) {
        let mut state = self.state.lock().unwrap();
        *state = CircuitState::Closed;
        self.failure_count.store(0, Ordering::Relaxed);
        println!("熔断器状态: HalfOpen -> Closed");
    }

    pub fn get_state(&self) -> CircuitState {
        self.state.lock().unwrap().clone()
    }
}

/// 限流器模式
#[allow(dead_code)]
pub struct RateLimiter {
    tokens: Arc<AtomicUsize>,
    max_tokens: usize,
    refill_rate: Duration,
    last_refill: Arc<Mutex<Instant>>,
}

impl RateLimiter {
    pub fn new(max_tokens: usize, refill_rate: Duration) -> Self {
        Self {
            tokens: Arc::new(AtomicUsize::new(max_tokens)),
            max_tokens,
            refill_rate,
            last_refill: Arc::new(Mutex::new(Instant::now())),
        }
    }

    pub fn try_acquire(&self) -> bool {
        self.refill_tokens();
        
        let current = self.tokens.load(Ordering::Relaxed);
        if current > 0 {
            self.tokens.fetch_sub(1, Ordering::Relaxed);
            true
        } else {
            false
        }
    }

    fn refill_tokens(&self) {
        let mut last_refill = self.last_refill.lock().unwrap();
        let now = Instant::now();
        
        if now - *last_refill >= self.refill_rate {
            let tokens_to_add = ((now - *last_refill).as_nanos() / self.refill_rate.as_nanos()) as usize;
            let current = self.tokens.load(Ordering::Relaxed);
            let new_tokens = (current + tokens_to_add).min(self.max_tokens);
            self.tokens.store(new_tokens, Ordering::Relaxed);
            *last_refill = now;
        }
    }

    pub fn get_available_tokens(&self) -> usize {
        self.refill_tokens();
        self.tokens.load(Ordering::Relaxed)
    }
}

/// 演示 Actor 模型
fn demo_actor_model() {
    println!("=== Actor 模型演示 ===");
    
    let actor = Actor::new("TestActor".to_string(), |message: String, state| {
        state.message_count += 1;
        state.last_message_time = Some(Instant::now());
        println!("Actor 收到消息: {}", message);
    });
    
    // 发送消息
    for i in 0..5 {
        actor.send(format!("消息 {}", i)).unwrap();
        thread::sleep(Duration::from_millis(100));
    }
    
    let state = actor.get_state();
    println!("Actor 状态: {:?}", state);
    
    actor.shutdown();
    println!();
}

/// 演示发布-订阅模式
fn demo_pub_sub() {
    println!("=== 发布-订阅模式演示 ===");
    
    let pubsub = PubSub::new();
    
    // 创建订阅者
    let sub1 = pubsub.subscribe("订阅者1".to_string());
    let sub2 = pubsub.subscribe("订阅者2".to_string());
    
    // 发布消息
    for i in 0..3 {
        pubsub.publish(format!("消息 {}", i)).unwrap();
        thread::sleep(Duration::from_millis(100));
    }
    
    // 接收消息
    for _ in 0..3 {
        if let Ok(msg) = sub1.try_recv() {
            println!("订阅者1 收到: {}", msg);
        }
        if let Ok(msg) = sub2.try_recv() {
            println!("订阅者2 收到: {}", msg);
        }
    }
    
    println!("订阅者数量: {}", pubsub.get_subscriber_count());
    println!();
}

/// 演示管道模式
fn demo_pipeline() {
    println!("=== 管道模式演示 ===");
    
    let pipeline = Pipeline::new();
    
    // 发送数据
    for i in 0..3 {
        pipeline.send(format!("数据 {}", i)).unwrap();
    }
    
    // 接收处理结果
    for _ in 0..3 {
        if let Ok(result) = pipeline.recv() {
            println!("管道输出: {}", result);
        }
    }
    println!();
}

/// 演示扇出-扇入模式
fn demo_fan_out_fan_in() {
    println!("=== 扇出-扇入模式演示 ===");
    
    let fan_out_fan_in = FanOutFanIn::new(3);
    
    // 发送数据
    for i in 0..5 {
        fan_out_fan_in.send(format!("任务 {}", i)).unwrap();
    }
    
    // 接收聚合结果
    for _ in 0..5 {
        if let Ok(result) = fan_out_fan_in.recv() {
            println!("{}", result);
        }
    }
    println!();
}

/// 演示熔断器模式
fn demo_circuit_breaker() {
    println!("=== 熔断器模式演示 ===");
    
    let circuit_breaker = CircuitBreaker::new(3, Duration::from_millis(500));
    
    // 模拟成功调用
    for i in 0..2 {
        let result: Result<String, String> = circuit_breaker.call(|| {
            println!("执行操作 {}", i);
            Ok(format!("成功 {}", i))
        });
        println!("结果: {:?}", result);
    }
    
    // 模拟失败调用
    for i in 2..5 {
        let result: Result<String, String> = circuit_breaker.call(|| {
            println!("执行操作 {} (失败)", i);
            Err("操作失败".to_string())
        });
        println!("结果: {:?}", result);
        println!("熔断器状态: {:?}", circuit_breaker.get_state());
    }
    
    // 等待超时
    thread::sleep(Duration::from_millis(600));
    
    // 尝试恢复
    let result: Result<String, String> = circuit_breaker.call(|| {
        println!("执行恢复操作");
        Ok("恢复成功".to_string())
    });
    println!("恢复结果: {:?}", result);
    println!("熔断器状态: {:?}", circuit_breaker.get_state());
    println!();
}

/// 演示限流器模式
fn demo_rate_limiter() {
    println!("=== 限流器模式演示 ===");
    
    let rate_limiter = RateLimiter::new(3, Duration::from_millis(1000));
    
    // 尝试获取令牌
    for i in 0..10 {
        if rate_limiter.try_acquire() {
            println!("操作 {} 获得令牌", i);
        } else {
            println!("操作 {} 被限流", i);
        }
        thread::sleep(Duration::from_millis(200));
    }
    
    println!("可用令牌: {}", rate_limiter.get_available_tokens());
    println!();
}

fn main() {
    println!("=== 高级并发模式示例 ===\n");
    
    demo_actor_model();
    demo_pub_sub();
    demo_pipeline();
    demo_fan_out_fan_in();
    demo_circuit_breaker();
    demo_rate_limiter();
    
    println!("=== 高级并发模式示例完成 ===");
}