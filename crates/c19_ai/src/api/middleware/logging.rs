//! 日志中间件
//! 
//! 提供HTTP请求日志记录功能

use axum::{
    extract::Request,
    middleware::Next,
    response::Response,
};
use tracing::{info, warn, error};
use std::time::Instant;

/// 日志中间件
pub async fn logging_middleware(
    request: Request,
    next: Next,
) -> Response {
    let start_time = Instant::now();
    let method = request.method().clone();
    let uri = request.uri().clone();
    let user_agent = request
        .headers()
        .get("User-Agent")
        .and_then(|h| h.to_str().ok())
        .unwrap_or("unknown");

    info!(
        method = %method,
        uri = %uri,
        user_agent = %user_agent,
        "Request started"
    );

    let response = next.run(request).await;
    let duration = start_time.elapsed();

    let status = response.status();
    let status_code = status.as_u16();

    match status_code {
        200..=299 => {
            info!(
                method = %method,
                uri = %uri,
                status = %status_code,
                duration_ms = %duration.as_millis(),
                "Request completed successfully"
            );
        }
        400..=499 => {
            warn!(
                method = %method,
                uri = %uri,
                status = %status_code,
                duration_ms = %duration.as_millis(),
                "Client error"
            );
        }
        500..=599 => {
            error!(
                method = %method,
                uri = %uri,
                status = %status_code,
                duration_ms = %duration.as_millis(),
                "Server error"
            );
        }
        _ => {
            info!(
                method = %method,
                uri = %uri,
                status = %status_code,
                duration_ms = %duration.as_millis(),
                "Request completed"
            );
        }
    }

    response
}
