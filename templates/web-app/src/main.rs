//! {{project_description}}
//!
//! A web application built with Axum and Rust.

use axum::{
    extract::State,
    http::StatusCode,
    response::Json,
    routing::{get, post},
    Router,
};
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;
use tower::ServiceBuilder;
use tower_http::{cors::CorsLayer, trace::TraceLayer};
use tracing::{info, Level};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

/// Application state
#[derive(Clone)]
pub struct AppState {
    /// Application configuration
    pub config: AppConfig,
}

/// Application configuration
#[derive(Debug, Clone)]
pub struct AppConfig {
    /// Server host
    pub host: String,

    /// Server port
    pub port: u16,

    /// Database URL
    pub database_url: String,

    /// JWT secret
    pub jwt_secret: String,
}

impl Default for AppConfig {
    fn default() -> Self {
        Self {
            host: "127.0.0.1".to_string(),
            port: 3000,
            database_url: "postgresql://localhost/{{project_name}}".to_string(),
            jwt_secret: "your-secret-key".to_string(),
        }
    }
}

/// Health check response
#[derive(Serialize)]
pub struct HealthResponse {
    pub status: String,
    pub version: String,
    pub timestamp: String,
}

/// API response wrapper
#[derive(Serialize)]
pub struct ApiResponse<T> {
    pub success: bool,
    pub data: Option<T>,
    pub error: Option<String>,
}

impl<T> ApiResponse<T> {
    pub fn success(data: T) -> Self {
        Self {
            success: true,
            data: Some(data),
            error: None,
        }
    }

    pub fn error(message: String) -> Self {
        Self {
            success: false,
            data: None,
            error: Some(message),
        }
    }
}

/// User data
#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct User {
    pub id: u32,
    pub name: String,
    pub email: String,
    pub created_at: String,
}

/// Create user request
#[derive(Debug, Deserialize)]
pub struct CreateUserRequest {
    pub name: String,
    pub email: String,
}

/// Create user response
#[derive(Debug, Serialize)]
pub struct CreateUserResponse {
    pub user: User,
    pub message: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize tracing
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "{{project_name}}=debug,tower_http=debug".into()),
        )
        .with(tracing_subscriber::fmt::layer())
        .init();

    // Load configuration
    let config = load_config().await?;

    // Create application state
    let state = AppState { config };

    // Build application
    let app = Router::new()
        .route("/", get(root))
        .route("/health", get(health))
        .route("/api/users", post(create_user))
        .route("/api/users/:id", get(get_user))
        .layer(
            ServiceBuilder::new()
                .layer(TraceLayer::new_for_http())
                .layer(CorsLayer::permissive()),
        )
        .with_state(state);

    // Start server
    let addr = SocketAddr::from(([127, 0, 0, 1], 3000));
    info!("Starting server on {}", addr);

    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;

    Ok(())
}

/// Load application configuration
async fn load_config() -> Result<AppConfig, Box<dyn std::error::Error>> {
    // In a real application, you would load this from environment variables or config files
    Ok(AppConfig::default())
}

/// Root endpoint
async fn root() -> &'static str {
    "{{project_description}} - Welcome!"
}

/// Health check endpoint
async fn health(State(state): State<AppState>) -> Json<HealthResponse> {
    Json(HealthResponse {
        status: "healthy".to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
        timestamp: chrono::Utc::now().to_rfc3339(),
    })
}

/// Create user endpoint
async fn create_user(
    State(state): State<AppState>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<Json<ApiResponse<CreateUserResponse>>, StatusCode> {
    // Validate input
    if payload.name.is_empty() || payload.email.is_empty() {
        return Ok(Json(ApiResponse::error(
            "Name and email are required".to_string(),
        )));
    }

    // Create user (in a real application, you would save to database)
    let user = User {
        id: 1, // In a real application, this would be generated
        name: payload.name.clone(),
        email: payload.email.clone(),
        created_at: chrono::Utc::now().to_rfc3339(),
    };

    let response = CreateUserResponse {
        user,
        message: "User created successfully".to_string(),
    };

    Ok(Json(ApiResponse::success(response)))
}

/// Get user endpoint
async fn get_user(
    State(state): State<AppState>,
    axum::extract::Path(id): axum::extract::Path<u32>,
) -> Result<Json<ApiResponse<User>>, StatusCode> {
    // In a real application, you would fetch from database
    let user = User {
        id,
        name: "John Doe".to_string(),
        email: "john@example.com".to_string(),
        created_at: chrono::Utc::now().to_rfc3339(),
    };

    Ok(Json(ApiResponse::success(user)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use axum::{
        body::Body,
        http::{Request, StatusCode},
        Router,
    };
    use tower::ServiceExt;

    async fn create_test_app() -> Router {
        let config = AppConfig::default();
        let state = AppState { config };

        Router::new()
            .route("/", get(root))
            .route("/health", get(health))
            .route("/api/users", post(create_user))
            .route("/api/users/:id", get(get_user))
            .with_state(state)
    }

    #[tokio::test]
    async fn test_root() {
        let app = create_test_app().await;

        let request = Request::builder().uri("/").body(Body::empty()).unwrap();

        let response = app.oneshot(request).await.unwrap();

        assert_eq!(response.status(), StatusCode::OK);
    }

    #[tokio::test]
    async fn test_health() {
        let app = create_test_app().await;

        let request = Request::builder()
            .uri("/health")
            .body(Body::empty())
            .unwrap();

        let response = app.oneshot(request).await.unwrap();

        assert_eq!(response.status(), StatusCode::OK);
    }

    #[tokio::test]
    async fn test_create_user() {
        let app = create_test_app().await;

        let user_data = CreateUserRequest {
            name: "John Doe".to_string(),
            email: "john@example.com".to_string(),
        };

        let request = Request::builder()
            .method("POST")
            .uri("/api/users")
            .header("content-type", "application/json")
            .body(Body::from(serde_json::to_vec(&user_data).unwrap()))
            .unwrap();

        let response = app.oneshot(request).await.unwrap();

        assert_eq!(response.status(), StatusCode::OK);
    }

    #[tokio::test]
    async fn test_get_user() {
        let app = create_test_app().await;

        let request = Request::builder()
            .uri("/api/users/1")
            .body(Body::empty())
            .unwrap();

        let response = app.oneshot(request).await.unwrap();

        assert_eq!(response.status(), StatusCode::OK);
    }
}
