// CSP (Communicating Sequential Processes) Model
//
// Implements Go-style channels and select for concurrent communication.
// Based on Tony Hoare's CSP and Go's channel implementation.

use crate::error_handling::prelude::*;
use std::fmt;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{mpsc, Mutex};
use tokio::time::timeout;

/// Channel for sending messages between processes
pub struct Channel<T> {
    sender: mpsc::Sender<T>,
    receiver: Arc<Mutex<mpsc::Receiver<T>>>,
}

impl<T> Clone for Channel<T> {
    fn clone(&self) -> Self {
        Self {
            sender: self.sender.clone(),
            receiver: Arc::clone(&self.receiver),
        }
    }
}

impl<T> Channel<T> {
    /// Create a new bounded channel
    pub fn bounded(capacity: usize) -> Self {
        let (tx, rx) = mpsc::channel(capacity);
        Self {
            sender: tx,
            receiver: Arc::new(Mutex::new(rx)),
        }
    }

    /// Create a new unbounded channel
    pub fn unbounded() -> (UnboundedSender<T>, UnboundedReceiver<T>) {
        let (tx, rx) = mpsc::unbounded_channel();
        (UnboundedSender { sender: tx }, UnboundedReceiver { receiver: rx })
    }

    /// Send a value through the channel
    pub async fn send(&self, value: T) -> Result<()> {
        self.sender.send(value).await.map_err(|_| {
            UnifiedError::new(
                "Failed to send: channel closed",
                ErrorSeverity::Medium,
                "csp",
                ErrorContext::new("csp", "send", file!(), line!(), ErrorSeverity::Medium, "csp"),
            )
        })
    }

    /// Try to send a value without blocking
    pub fn try_send(&self, value: T) -> Result<()> {
        self.sender.try_send(value).map_err(|e| {
            let msg = match e {
                mpsc::error::TrySendError::Full(_) => "Channel is full",
                mpsc::error::TrySendError::Closed(_) => "Channel is closed",
            };
            UnifiedError::new(
                msg,
                ErrorSeverity::Low,
                "csp",
                ErrorContext::new("csp", "try_send", file!(), line!(), ErrorSeverity::Low, "csp"),
            )
        })
    }

    /// Receive a value from the channel
    pub async fn recv(&self) -> Option<T> {
        let mut rx = self.receiver.lock().await;
        rx.recv().await
    }

    /// Try to receive a value without blocking
    pub async fn try_recv(&self) -> Result<T> {
        let mut rx = self.receiver.lock().await;
        rx.try_recv().map_err(|e| {
            let msg = match e {
                mpsc::error::TryRecvError::Empty => "Channel is empty",
                mpsc::error::TryRecvError::Disconnected => "Channel is closed",
            };
            UnifiedError::new(
                msg,
                ErrorSeverity::Low,
                "csp",
                ErrorContext::new("csp", "try_recv", file!(), line!(), ErrorSeverity::Low, "csp"),
            )
        })
    }

    /// Receive with timeout
    pub async fn recv_timeout(&self, duration: Duration) -> Result<T> {
        match timeout(duration, self.recv()).await {
            Ok(Some(value)) => Ok(value),
            Ok(None) => Err(UnifiedError::new(
                "Channel closed",
                ErrorSeverity::Medium,
                "csp",
                ErrorContext::new(
                    "csp",
                    "recv_timeout",
                    file!(),
                    line!(),
                    ErrorSeverity::Medium,
                    "csp",
                ),
            )),
            Err(_) => Err(UnifiedError::new(
                "Receive timeout",
                ErrorSeverity::Low,
                "csp",
                ErrorContext::new(
                    "csp",
                    "recv_timeout",
                    file!(),
                    line!(),
                    ErrorSeverity::Low,
                    "csp",
                ),
            )),
        }
    }

    /// Get a sender clone
    pub fn sender(&self) -> mpsc::Sender<T> {
        self.sender.clone()
    }
}

impl<T> fmt::Debug for Channel<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Channel").finish()
    }
}

/// Unbounded sender
pub struct UnboundedSender<T> {
    sender: mpsc::UnboundedSender<T>,
}

impl<T> UnboundedSender<T> {
    pub fn send(&self, value: T) -> Result<()> {
        self.sender.send(value).map_err(|_| {
            UnifiedError::new(
                "Failed to send: channel closed",
                ErrorSeverity::Medium,
                "csp",
                ErrorContext::new("csp", "send", file!(), line!(), ErrorSeverity::Medium, "csp"),
            )
        })
    }
}

impl<T> Clone for UnboundedSender<T> {
    fn clone(&self) -> Self {
        Self {
            sender: self.sender.clone(),
        }
    }
}

/// Unbounded receiver
pub struct UnboundedReceiver<T> {
    receiver: mpsc::UnboundedReceiver<T>,
}

impl<T> UnboundedReceiver<T> {
    pub async fn recv(&mut self) -> Option<T> {
        self.receiver.recv().await
    }

    pub fn try_recv(&mut self) -> Result<T> {
        self.receiver.try_recv().map_err(|e| {
            let msg = match e {
                mpsc::error::TryRecvError::Empty => "Channel is empty",
                mpsc::error::TryRecvError::Disconnected => "Channel is closed",
            };
            UnifiedError::new(
                msg,
                ErrorSeverity::Low,
                "csp",
                ErrorContext::new("csp", "try_recv", file!(), line!(), ErrorSeverity::Low, "csp"),
            )
        })
    }
}

/// Select operation for multiplexing channels
pub struct Select<'a, T> {
    cases: Vec<SelectCase<'a, T>>,
}

enum SelectCase<'a, T> {
    Recv(&'a Channel<T>),
    Send(&'a Channel<T>, T),
    Default,
}

impl<'a, T: Clone> Select<'a, T> {
    pub fn new() -> Self {
        Self { cases: Vec::new() }
    }

    /// Add a receive case
    pub fn recv(mut self, channel: &'a Channel<T>) -> Self {
        self.cases.push(SelectCase::Recv(channel));
        self
    }

    /// Add a send case
    pub fn send(mut self, channel: &'a Channel<T>, value: T) -> Self {
        self.cases.push(SelectCase::Send(channel, value));
        self
    }

    /// Add a default case (non-blocking)
    pub fn default(mut self) -> Self {
        self.cases.push(SelectCase::Default);
        self
    }

    /// Execute the select operation
    pub async fn execute(self) -> SelectResult<T> {
        // Simplified select: just try each case in order
        for case in self.cases {
            match case {
                SelectCase::Recv(ch) => {
                    if let Ok(value) = ch.try_recv().await {
                        return SelectResult::Received(value);
                    }
                }
                SelectCase::Send(ch, value) => {
                    if ch.try_send(value.clone()).is_ok() {
                        return SelectResult::Sent;
                    }
                }
                SelectCase::Default => {
                    return SelectResult::Default;
                }
            }
        }
        SelectResult::Default
    }
}

impl<'a, T: Clone> Default for Select<'a, T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Result of a select operation
#[derive(Debug)]
pub enum SelectResult<T> {
    Received(T),
    Sent,
    Default,
}

/// Process represents a concurrent computation unit in CSP
pub struct Process {
    name: String,
    handle: Option<tokio::task::JoinHandle<Result<()>>>,
}

impl Process {
    /// Spawn a new process
    pub fn spawn<F>(name: impl Into<String>, f: F) -> Self
    where
        F: std::future::Future<Output = Result<()>> + Send + 'static,
    {
        let handle = tokio::spawn(f);
        Self {
            name: name.into(),
            handle: Some(handle),
        }
    }

    /// Wait for the process to complete
    pub async fn join(mut self) -> Result<()> {
        if let Some(handle) = self.handle.take() {
            handle.await.map_err(|e| {
                UnifiedError::new(
                    format!("Process {} panicked: {}", self.name, e),
                    ErrorSeverity::High,
                    "csp",
                    ErrorContext::new("csp", "join", file!(), line!(), ErrorSeverity::High, "csp"),
                )
            })??;
        }
        Ok(())
    }

    /// Get process name
    pub fn name(&self) -> &str {
        &self.name
    }
}

impl fmt::Debug for Process {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Process")
            .field("name", &self.name)
            .finish()
    }
}

/// Barrier for synchronizing multiple processes
pub struct Barrier {
    inner: Arc<tokio::sync::Barrier>,
}

impl Barrier {
    pub fn new(n: usize) -> Self {
        Self {
            inner: Arc::new(tokio::sync::Barrier::new(n)),
        }
    }

    pub async fn wait(&self) {
        self.inner.wait().await;
    }
}

impl Clone for Barrier {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

/// Pipeline builder for creating processing pipelines
pub struct Pipeline<T> {
    stages: Vec<Box<dyn Fn(T) -> T + Send + Sync>>,
}

impl<T: Send + 'static> Pipeline<T> {
    pub fn new() -> Self {
        Self { stages: Vec::new() }
    }

    pub fn add_stage<F>(mut self, f: F) -> Self
    where
        F: Fn(T) -> T + Send + Sync + 'static,
    {
        self.stages.push(Box::new(f));
        self
    }

    pub fn process(&self, mut value: T) -> T {
        for stage in &self.stages {
            value = stage(value);
        }
        value
    }

    pub async fn process_async<I>(
        &self,
        input: Channel<T>,
        output: Channel<T>,
    ) -> Result<()>
    where
        T: Clone,
    {
        while let Some(value) = input.recv().await {
            let processed = self.process(value);
            output.send(processed).await?;
        }
        Ok(())
    }
}

impl<T: Send + 'static> Default for Pipeline<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Fan-out pattern: send to multiple channels
pub async fn fan_out<T: Clone>(
    input: &Channel<T>,
    outputs: Vec<&Channel<T>>,
) -> Result<()> {
    while let Some(value) = input.recv().await {
        for output in &outputs {
            output.send(value.clone()).await?;
        }
    }
    Ok(())
}

/// Fan-in pattern: receive from multiple channels
pub async fn fan_in<T: Send + 'static>(
    inputs: Vec<Channel<T>>,
    output: Channel<T>,
) -> Result<()> {
    let mut handles = Vec::new();

    for input in inputs {
        let output_clone = output.clone();
        let handle = tokio::spawn(async move {
            while let Some(value) = input.recv().await {
                output_clone.send(value).await.ok();
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await.ok();
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_channel_send_recv() {
        let ch = Channel::<i32>::bounded(10);

        ch.send(42).await.unwrap();
        let value = ch.recv().await.unwrap();

        assert_eq!(value, 42);
    }

    #[tokio::test]
    async fn test_unbounded_channel() {
        let (tx, mut rx) = Channel::<String>::unbounded();

        tx.send("hello".to_string()).unwrap();
        tx.send("world".to_string()).unwrap();

        assert_eq!(rx.recv().await, Some("hello".to_string()));
        assert_eq!(rx.recv().await, Some("world".to_string()));
    }

    #[tokio::test]
    async fn test_channel_timeout() {
        let ch = Channel::<i32>::bounded(10);

        let result = ch.recv_timeout(Duration::from_millis(100)).await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_process_spawn() {
        let process = Process::spawn("test", async {
            tokio::time::sleep(Duration::from_millis(10)).await;
            Ok(())
        });

        process.join().await.unwrap();
    }

    #[tokio::test]
    async fn test_barrier() {
        let barrier = Barrier::new(3);
        let mut handles = Vec::new();

        for i in 0..3 {
            let barrier_clone = barrier.clone();
            let handle = tokio::spawn(async move {
                println!("Process {} waiting", i);
                barrier_clone.wait().await;
                println!("Process {} passed barrier", i);
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.await.unwrap();
        }
    }

    #[tokio::test]
    async fn test_pipeline() {
        let pipeline = Pipeline::new()
            .add_stage(|x: i32| x * 2)
            .add_stage(|x: i32| x + 10)
            .add_stage(|x: i32| x * x);

        let result = pipeline.process(5);
        assert_eq!(result, 400); // ((5 * 2) + 10)^2 = 20^2 = 400
    }

    #[tokio::test]
    async fn test_fan_out() {
        let input = Channel::<i32>::bounded(10);
        let out1 = Channel::<i32>::bounded(10);
        let out2 = Channel::<i32>::bounded(10);

        // Clone channels for the spawned task
        let input_clone = input.clone();
        let out1_clone = out1.clone();
        let out2_clone = out2.clone();

        tokio::spawn(async move {
            fan_out(&input_clone, vec![&out1_clone, &out2_clone]).await.ok();
        });

        input.send(42).await.unwrap();
        
        // Give time for fan_out to process
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;

        assert_eq!(out1.recv().await, Some(42));
        assert_eq!(out2.recv().await, Some(42));
    }
}

