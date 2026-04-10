//! Unified error handling module
use std::time::Duration;
use thiserror::Error;

#[derive(Error, Debug, Clone)]
pub enum RustLangError {
    #[error("ownership error: {0}")]
    Ownership(#[from] OwnershipError),
    #[error("type error: {0}")]
    Type(#[from] TypeError),
    #[error("control flow error: {0}")]
    ControlFlow(#[from] ControlFlowError),
    #[error("generic error: {0}")]
    Generic(#[from] GenericError),
    #[error("thread error: {0}")]
    Thread(#[from] ThreadError),
    #[error("async error: {0}")]
    Async(#[from] AsyncError),
    #[error("process error: {0}")]
    Process(#[from] ProcessError),
    #[error("algorithm error: {0}")]
    Algorithm(#[from] AlgorithmError),
    #[error("design pattern error: {0}")]
    DesignPattern(#[from] DesignPatternError),
    #[error("network error: {0}")]
    Network(#[from] NetworkError),
    #[error("macro error: {0}")]
    Macro(#[from] MacroError),
    #[error("wasm error: {0}")]
    Wasm(#[from] WasmError),
    #[error("IO error: {0}")]
    Io(String),
    #[error("config error: {0}")]
    Config(String),
    #[error("other error: {0}")]
    Other(String),
}

pub type Result<T> = std::result::Result<T, RustLangError>;

#[derive(Error, Debug, Clone)]
pub enum OwnershipError {
    #[error("borrow conflict: {0}")]
    BorrowConflict(String),
    #[error("lifetime error: {0}")]
    Lifetime(String),
    #[error("move error: {0}")]
    MoveError(String),
    #[error("mutable borrow conflict: {0}")]
    MutableBorrowConflict(String),
    #[error("interior mutability error: {0}")]
    InteriorMutability(String),
    #[error("memory safety error: {0}")]
    MemorySafety(String),
}

#[derive(Error, Debug, Clone)]
pub enum TypeError {
    #[error("type mismatch: expected {expected}, found {found}")]
    TypeMismatch { expected: String, found: String },
    #[error("inference failed: {0}")]
    InferenceFailed(String),
    #[error("trait bound not satisfied: {0}")]
    TraitBoundNotSatisfied(String),
    #[error("conversion error: {0}")]
    Conversion(String),
    #[error("null pointer: {0}")]
    NullPointer(String),
    #[error("variance error: {0}")]
    Variance(String),
}

#[derive(Error, Debug, Clone)]
pub enum ControlFlowError {
    #[error("non-exhaustive match: {0}")]
    NonExhaustiveMatch(String),
    #[error("stack overflow: {0}")]
    StackOverflow(String),
    #[error("interrupted: {0}")]
    Interrupted(String),
    #[error("closure capture error: {0}")]
    ClosureCapture(String),
    #[error("generator error: {0}")]
    Generator(String),
}

#[derive(Error, Debug, Clone)]
pub enum GenericError {
    #[error("type parameter mismatch: {0}")]
    TypeParameterMismatch(String),
    #[error("associated type error: {0}")]
    AssociatedType(String),
    #[error("constraint conflict: {0}")]
    ConstraintConflict(String),
    #[error("GAT error: {0}")]
    GatError(String),
    #[error("HRTB error: {0}")]
    HrtbError(String),
}

#[derive(Error, Debug, Clone)]
pub enum ThreadError {
    #[error("creation failed: {0}")]
    CreationFailed(String),
    #[error("panicked: {0}")]
    Panicked(String),
    #[error("deadlock detected: {0}")]
    Deadlock(String),
    #[error("data race: {0}")]
    DataRace(String),
    #[error("lock acquisition failed: {0}")]
    LockAcquisition(String),
    #[error("send error: {0}")]
    SendError(String),
    #[error("receive error: {0}")]
    ReceiveError(String),
    #[error("lock-free error: {0}")]
    LockFree(String),
}

#[derive(Error, Debug, Clone)]
pub enum AsyncError {
    #[error("cancelled: {0}")]
    Cancelled(String),
    #[error("timeout: {0:?}")]
    Timeout(Duration),
    #[error("runtime error: {0}")]
    Runtime(String),
    #[error("scheduler error: {0}")]
    Scheduler(String),
    #[error("stream error: {0}")]
    Stream(String),
    #[error("backpressure error: {0}")]
    Backpressure(String),
}

#[derive(Error, Debug, Clone)]
pub enum ProcessError {
    #[error("creation failed: {0}")]
    CreationFailed(String),
    #[error("start failed: {0}")]
    StartFailed(String),
    #[error("wait failed: {0}")]
    WaitFailed(String),
    #[error("termination failed: {0}")]
    TerminationFailed(String),
    #[error("not found: {0}")]
    NotFound(u32),
    #[error("permission denied: {0}")]
    PermissionDenied(String),
    #[error("already terminated")]
    AlreadyTerminated,
    #[error("IPC error: {0}")]
    Ipc(String),
    #[error("signal error: {0}")]
    Signal(String),
    #[error("{0}")]
    Other(String),
}

#[derive(Error, Debug, Clone)]
pub enum AlgorithmError {
    #[error("invalid input: {0}")]
    InvalidInput(String),
    #[error("not implemented: {0}")]
    NotImplemented(String),
    #[error("complexity exceeded: {0}")]
    ComplexityExceeded(String),
    #[error("numeric overflow: {0}")]
    NumericOverflow(String),
    #[error("convergence failed: {0}")]
    ConvergenceFailed(String),
    #[error("data structure error: {0}")]
    DataStructure(String),
}

#[derive(Error, Debug, Clone)]
pub enum DesignPatternError {
    #[error("singleton error: {0}")]
    Singleton(String),
    #[error("factory error: {0}")]
    Factory(String),
    #[error("proxy error: {0}")]
    Proxy(String),
    #[error("flyweight error: {0}")]
    Flyweight(String),
    #[error("chain error: {0}")]
    Chain(String),
    #[error("observer error: {0}")]
    Observer(String),
    #[error("concurrency error: {0}")]
    Concurrency(String),
}

#[derive(Error, Debug, Clone)]
pub enum NetworkError {
    #[error("connection error: {0}")]
    Connection(String),
    #[error("protocol error: {0}")]
    Protocol(String),
    #[error("timeout: {0:?}")]
    Timeout(Duration),
    #[error("DNS error: {0}")]
    Dns(String),
    #[error("TLS error: {0}")]
    Tls(String),
    #[error("HTTP error: status={status}, message={message}")]
    Http { status: u16, message: String },
    #[error("WebSocket error: {0}")]
    WebSocket(String),
    #[error("authentication error: {0}")]
    Authentication(String),
    #[error("buffer error: {0}")]
    Buffer(String),
}

#[derive(Error, Debug, Clone)]
pub enum MacroError {
    #[error("parse error: {0}")]
    ParseError(String),
    #[error("expansion error: {0}")]
    ExpansionError(String),
    #[error("proc macro error: {0}")]
    ProcMacro(String),
    #[error("decl macro error: {0}")]
    DeclMacro(String),
    #[error("hygiene error: {0}")]
    Hygiene(String),
}

#[derive(Error, Debug, Clone)]
pub enum WasmError {
    #[error("compilation error: {0}")]
    Compilation(String),
    #[error("runtime error: {0}")]
    Runtime(String),
    #[error("memory error: {0}")]
    Memory(String),
    #[error("import error: {0}")]
    Import(String),
    #[error("export error: {0}")]
    Export(String),
    #[error("WASI error: {0}")]
    Wasi(String),
    #[error("bindgen error: {0}")]
    Bindgen(String),
}

pub trait ErrorRecovery {
    fn is_retryable(&self) -> bool;
    fn retry_delay(&self) -> Option<Duration>;
    fn max_retries(&self) -> Option<u32>;
}

impl ErrorRecovery for RustLangError {
    fn is_retryable(&self) -> bool {
        matches!(self,
            RustLangError::Network(NetworkError::Timeout(_) | NetworkError::Connection(_)) |
            RustLangError::Async(AsyncError::Timeout(_) | AsyncError::Backpressure(_)) |
            RustLangError::Process(ProcessError::StartFailed(_) | ProcessError::Ipc(_)) |
            RustLangError::Thread(ThreadError::LockAcquisition(_) | ThreadError::SendError(_))
        )
    }

    fn retry_delay(&self) -> Option<Duration> {
        match self {
            RustLangError::Network(e) => match e {
                NetworkError::Timeout(_) => Some(Duration::from_millis(100)),
                NetworkError::Connection(_) => Some(Duration::from_millis(500)),
                _ => None,
            },
            RustLangError::Async(_) => Some(Duration::from_millis(50)),
            RustLangError::Process(_) => Some(Duration::from_millis(200)),
            RustLangError::Thread(_) => Some(Duration::from_millis(10)),
            _ => None,
        }
    }

    fn max_retries(&self) -> Option<u32> {
        match self {
            RustLangError::Network(e) => match e {
                NetworkError::Timeout(_) => Some(3),
                NetworkError::Connection(_) => Some(5),
                _ => None,
            },
            RustLangError::Async(_) => Some(3),
            RustLangError::Process(_) => Some(3),
            RustLangError::Thread(_) => Some(5),
            _ => None,
        }
    }
}

pub trait ErrorContext<T> {
    fn with_context<F>(self, f: F) -> Result<T> where F: FnOnce() -> String;
}

impl<T, E> ErrorContext<T> for std::result::Result<T, E> where E: Into<RustLangError> {
    fn with_context<F>(self, _f: F) -> Result<T> where F: FnOnce() -> String {
        self.map_err(|e| e.into())
    }
}

impl From<std::io::Error> for RustLangError {
    fn from(e: std::io::Error) -> Self {
        RustLangError::Io(e.to_string())
    }
}

impl From<String> for RustLangError {
    fn from(s: String) -> Self { RustLangError::Other(s) }
}

impl From<&str> for RustLangError {
    fn from(s: &str) -> Self { RustLangError::Other(s.to_string()) }
}

// 向后兼容：Retryable 是 ErrorRecovery 的别名
pub use ErrorRecovery as Retryable;
