//! C05: 线程和并发错误处理

pub use common::{
    ThreadError, RustLangError, Result,
    ErrorContext, ErrorRecovery,
};

/// C05 crate 的结果类型
pub type C05Result<T> = Result<T>;

/// 创建线程创建失败错误
pub fn thread_creation_failed<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Thread(ThreadError::CreationFailed(msg.into()))
}

/// 创建线程 panic 错误
pub fn thread_panicked<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Thread(ThreadError::Panicked(msg.into()))
}

/// 创建死锁检测错误
pub fn deadlock_detected<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Thread(ThreadError::Deadlock(msg.into()))
}

/// 创建数据竞争错误
pub fn data_race<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Thread(ThreadError::DataRace(msg.into()))
}

/// 创建锁获取失败错误
pub fn lock_acquisition_failed<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Thread(ThreadError::LockAcquisition(msg.into()))
}

/// 创建发送错误
pub fn send_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Thread(ThreadError::SendError(msg.into()))
}

/// 创建接收错误
pub fn receive_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Thread(ThreadError::ReceiveError(msg.into()))
}

/// 创建无锁数据结构错误
pub fn lock_free_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Thread(ThreadError::LockFree(msg.into()))
}
