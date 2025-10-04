// Actor Model Implementation
//
// Provides a lightweight actor system for concurrent computation based on
// message passing. Inspired by Erlang/Akka actor systems.
//
// Key features:
// - Isolated state (no shared memory)
// - Asynchronous message passing
// - Supervision and fault tolerance
// - Location transparency

use crate::error_handling::prelude::*;
use async_trait::async_trait;
use std::any::Any;
use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;
use tokio::sync::mpsc::{self, UnboundedReceiver, UnboundedSender};
use tokio::sync::RwLock;
use uuid::Uuid;

/// Unique identifier for an actor
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct ActorId(String);

impl ActorId {
    pub fn new(id: impl Into<String>) -> Self {
        Self(id.into())
    }

    pub fn random() -> Self {
        Self(Uuid::new_v4().to_string())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for ActorId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Actor({})", self.0)
    }
}

/// Actor address for sending messages
#[derive(Clone)]
pub struct ActorRef {
    id: ActorId,
    sender: UnboundedSender<Box<dyn ActorMessage>>,
}

impl ActorRef {
    pub fn new(id: ActorId, sender: UnboundedSender<Box<dyn ActorMessage>>) -> Self {
        Self { id, sender }
    }

    pub fn id(&self) -> &ActorId {
        &self.id
    }

    /// Send a message to the actor
    pub fn send<M: ActorMessage>(&self, message: M) -> Result<()> {
        self.sender
            .send(Box::new(message))
            .map_err(|_| {
                UnifiedError::new(
                    format!("Failed to send message to actor {}", self.id),
                    ErrorSeverity::Medium,
                    "actor",
                    ErrorContext::new(
                        "actor",
                        "send",
                        file!(),
                        line!(),
                        ErrorSeverity::Medium,
                        "actor",
                    ),
                )
            })
    }

    /// Send a message and wait for response
    pub async fn ask<M, R>(&self, message: M) -> Result<R>
    where
        M: ActorMessage + 'static,
        R: Any + Send + 'static,
    {
        // Create a oneshot channel for the response
        let (tx, rx) = tokio::sync::oneshot::channel();

        // Wrap message with response channel
        let wrapped = AskMessage {
            message: Box::new(message),
            respond_to: tx,
        };

        self.send(wrapped)?;

        // Wait for response
        rx.await
            .map_err(|_| {
                UnifiedError::new(
                    "Actor did not respond",
                    ErrorSeverity::Medium,
                    "actor",
                    ErrorContext::new(
                        "actor",
                        "ask",
                        file!(),
                        line!(),
                        ErrorSeverity::Medium,
                        "actor",
                    ),
                )
            })?
            .downcast::<R>()
            .map(|boxed| *boxed)
            .map_err(|_| {
                UnifiedError::new(
                    "Failed to downcast response",
                    ErrorSeverity::Medium,
                    "actor",
                    ErrorContext::new(
                        "actor",
                        "ask",
                        file!(),
                        line!(),
                        ErrorSeverity::Medium,
                        "actor",
                    ),
                )
            })
    }
}

impl fmt::Debug for ActorRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ActorRef").field("id", &self.id).finish()
    }
}

/// Message that can be sent to an actor
pub trait ActorMessage: Send + 'static {
    fn as_any(&self) -> &dyn Any;
    fn as_any_mut(&mut self) -> &mut dyn Any;
}

impl<T: Send + 'static> ActorMessage for T {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

/// Internal message for request-response pattern
#[allow(dead_code)]
struct AskMessage {
    message: Box<dyn ActorMessage>,
    respond_to: tokio::sync::oneshot::Sender<Box<dyn Any + Send>>,
}

// Manual implementation to avoid blanket impl conflict
unsafe impl Send for AskMessage {}

#[allow(dead_code)]
impl AskMessage {
    fn as_any_impl(&self) -> &dyn Any {
        self
    }

    fn as_any_mut_impl(&mut self) -> &mut dyn Any {
        self
    }
}

/// Actor lifecycle hooks
#[async_trait]
pub trait Actor: Send + 'static {
    /// Called when the actor is started
    async fn pre_start(&mut self) -> Result<()> {
        Ok(())
    }

    /// Called when the actor is stopped
    async fn post_stop(&mut self) -> Result<()> {
        Ok(())
    }

    /// Handle incoming message
    async fn receive(&mut self, message: Box<dyn ActorMessage>, ctx: &ActorContext) -> Result<()>;

    /// Handle actor failure
    #[allow(unused_variables)]
    async fn on_failure(&mut self, error: UnifiedError) -> SupervisorDirective {
        SupervisorDirective::Restart
    }
}

/// Supervisor directive for handling actor failures
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SupervisorDirective {
    /// Resume the actor (ignore the error)
    Resume,
    /// Restart the actor
    Restart,
    /// Stop the actor
    Stop,
    /// Escalate to parent supervisor
    Escalate,
}

/// Actor execution context
pub struct ActorContext {
    id: ActorId,
    system: ActorSystem,
    self_ref: Option<ActorRef>,
}

impl ActorContext {
    pub fn new(id: ActorId, system: ActorSystem) -> Self {
        Self {
            id,
            system,
            self_ref: None,
        }
    }

    pub fn id(&self) -> &ActorId {
        &self.id
    }

    pub fn system(&self) -> &ActorSystem {
        &self.system
    }

    pub fn self_ref(&self) -> Option<&ActorRef> {
        self.self_ref.as_ref()
    }

    pub fn set_self_ref(&mut self, actor_ref: ActorRef) {
        self.self_ref = Some(actor_ref);
    }

    /// Spawn a child actor
    pub async fn spawn<A: Actor>(&self, actor: A) -> Result<ActorRef> {
        self.system.spawn(actor).await
    }

    /// Stop an actor
    pub async fn stop(&self, actor_id: &ActorId) -> Result<()> {
        self.system.stop(actor_id).await
    }
}

/// Actor system configuration
#[derive(Debug, Clone)]
pub struct ActorSystemConfig {
    pub name: String,
    pub default_mailbox_size: usize,
}

impl Default for ActorSystemConfig {
    fn default() -> Self {
        Self {
            name: "default".to_string(),
            default_mailbox_size: 1000,
        }
    }
}

/// Actor system manages actor lifecycle
#[derive(Clone)]
pub struct ActorSystem {
    inner: Arc<ActorSystemInner>,
}

struct ActorSystemInner {
    config: ActorSystemConfig,
    actors: RwLock<HashMap<ActorId, ActorRef>>,
}

impl ActorSystem {
    pub fn new(config: ActorSystemConfig) -> Self {
        Self {
            inner: Arc::new(ActorSystemInner {
                config,
                actors: RwLock::new(HashMap::new()),
            }),
        }
    }

    pub fn default() -> Self {
        Self::new(ActorSystemConfig::default())
    }

    pub fn config(&self) -> &ActorSystemConfig {
        &self.inner.config
    }

    /// Spawn a new actor
    pub async fn spawn<A: Actor>(&self, mut actor: A) -> Result<ActorRef> {
        let actor_id = ActorId::random();
        let (tx, rx) = mpsc::unbounded_channel();
        let actor_ref = ActorRef::new(actor_id.clone(), tx);

        // Create actor context
        let mut ctx = ActorContext::new(actor_id.clone(), self.clone());
        ctx.set_self_ref(actor_ref.clone());

        // Call pre_start hook
        actor.pre_start().await?;

        // Store actor reference
        self.inner
            .actors
            .write()
            .await
            .insert(actor_id.clone(), actor_ref.clone());

        // Spawn actor task
        let system = self.clone();
        tokio::spawn(async move {
            if let Err(e) = Self::run_actor(actor, rx, ctx, system).await {
                eprintln!("Actor {} failed: {}", actor_id, e);
            }
        });

        Ok(actor_ref)
    }

    /// Stop an actor
    pub async fn stop(&self, actor_id: &ActorId) -> Result<()> {
        let mut actors = self.inner.actors.write().await;
        if actors.remove(actor_id).is_some() {
            Ok(())
        } else {
            Err(UnifiedError::new(
                format!("Actor {} not found", actor_id),
                ErrorSeverity::Low,
                "actor",
                ErrorContext::new(
                    "actor",
                    "stop",
                    file!(),
                    line!(),
                    ErrorSeverity::Low,
                    "actor",
                ),
            ))
        }
    }

    /// Get actor reference by ID
    pub async fn get_actor(&self, actor_id: &ActorId) -> Option<ActorRef> {
        self.inner.actors.read().await.get(actor_id).cloned()
    }

    /// Get all active actors
    pub async fn list_actors(&self) -> Vec<ActorId> {
        self.inner.actors.read().await.keys().cloned().collect()
    }

    /// Shutdown the actor system
    pub async fn shutdown(&self) -> Result<()> {
        let actor_ids: Vec<ActorId> = self.list_actors().await;
        for actor_id in actor_ids {
            self.stop(&actor_id).await?;
        }
        Ok(())
    }

    // Internal: Run actor event loop
    async fn run_actor<A: Actor>(
        mut actor: A,
        mut rx: UnboundedReceiver<Box<dyn ActorMessage>>,
        ctx: ActorContext,
        system: ActorSystem,
    ) -> Result<()> {
        while let Some(message) = rx.recv().await {
            match actor.receive(message, &ctx).await {
                Ok(_) => {}
                Err(e) => {
                    let directive = actor.on_failure(e).await;
                    match directive {
                        SupervisorDirective::Resume => continue,
                        SupervisorDirective::Restart => {
                            // Restart actor
                            actor.post_stop().await?;
                            actor.pre_start().await?;
                        }
                        SupervisorDirective::Stop => {
                            actor.post_stop().await?;
                            system.stop(ctx.id()).await?;
                            break;
                        }
                        SupervisorDirective::Escalate => {
                            // In a real system, this would escalate to parent
                            actor.post_stop().await?;
                            system.stop(ctx.id()).await?;
                            break;
                        }
                    }
                }
            }
        }

        actor.post_stop().await?;
        Ok(())
    }
}

/// Helper macro for creating actors
#[macro_export]
macro_rules! actor {
    ($name:ident { $($field:ident: $ty:ty),* $(,)? } $($rest:tt)*) => {
        pub struct $name {
            $(pub $field: $ty),*
        }

        #[async_trait::async_trait]
        impl Actor for $name $($rest)*
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    // Simple counter actor for testing
    struct CounterActor {
        count: i32,
    }

    #[derive(Debug)]
    struct Increment;

    #[derive(Debug)]
    struct GetCount;

    #[async_trait]
    impl Actor for CounterActor {
        async fn receive(
            &mut self,
            message: Box<dyn ActorMessage>,
            _ctx: &ActorContext,
        ) -> Result<()> {
            if let Some(_inc) = message.as_any().downcast_ref::<Increment>() {
                self.count += 1;
            } else if let Some(_get) = message.as_any().downcast_ref::<GetCount>() {
                // In a real implementation, we'd send back the count
                println!("Current count: {}", self.count);
            }
            Ok(())
        }
    }

    #[tokio::test]
    async fn test_actor_creation() {
        let system = ActorSystem::default();
        let actor = CounterActor { count: 0 };
        let actor_ref = system.spawn(actor).await.unwrap();

        assert!(system.get_actor(actor_ref.id()).await.is_some());
    }

    #[tokio::test]
    async fn test_actor_messaging() {
        let system = ActorSystem::default();
        let actor = CounterActor { count: 0 };
        let actor_ref = system.spawn(actor).await.unwrap();

        // Send messages
        actor_ref.send(Increment).unwrap();
        actor_ref.send(Increment).unwrap();
        actor_ref.send(GetCount).unwrap();

        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    }

    #[tokio::test]
    async fn test_actor_stop() {
        let system = ActorSystem::default();
        let actor = CounterActor { count: 0 };
        let actor_ref = system.spawn(actor).await.unwrap();

        let actor_id = actor_ref.id().clone();
        system.stop(&actor_id).await.unwrap();

        assert!(system.get_actor(&actor_id).await.is_none());
    }

    #[tokio::test]
    async fn test_actor_system_shutdown() {
        let system = ActorSystem::default();

        for _ in 0..5 {
            let actor = CounterActor { count: 0 };
            system.spawn(actor).await.unwrap();
        }

        assert_eq!(system.list_actors().await.len(), 5);

        system.shutdown().await.unwrap();

        assert_eq!(system.list_actors().await.len(), 0);
    }
}

