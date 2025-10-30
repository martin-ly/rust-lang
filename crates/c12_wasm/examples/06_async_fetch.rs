//! # 异步 Fetch 示例
//!
//! 展示如何在 WASM 中使用异步编程和 Fetch API
//!
//! ## JavaScript 使用示例
//!
//! ```javascript
//! import init, { fetch_text, fetch_json } from './pkg/c12_wasm.js';
//!
//! await init();
//!
//! // 获取文本
//! const text = await fetch_text('https://api.example.com/data');
//! console.log(text);
//!
//! // 获取 JSON
//! const json = await fetch_json('https://api.example.com/users');
//! console.log(json);
//! ```

use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::JsFuture;
use web_sys::{Request, RequestInit, RequestMode, Response};

/// 使用 Fetch API 获取文本内容
///
/// # 参数
/// - `url`: 要请求的 URL
///
/// # 返回值
/// 返回 Promise，成功时包含文本内容，失败时包含错误信息
///
/// # 示例
/// ```javascript
/// const text = await fetch_text('https://example.com/data.txt');
/// console.log(text);
/// ```
#[wasm_bindgen]
pub async fn fetch_text(url: String) -> Result<String, JsValue> {
    let opts = RequestInit::new();
    opts.set_method("GET");
    opts.set_mode(RequestMode::Cors);

    let request = Request::new_with_str(&url)?;

    let window = web_sys::window().ok_or_else(|| JsValue::from_str("No window object"))?;
    let resp_value = JsFuture::from(window.fetch_with_request(&request)).await?;
    let resp: Response = resp_value.dyn_into()?;

    if !resp.ok() {
        return Err(JsValue::from_str(&format!("HTTP error: {}", resp.status())));
    }

    let text_promise = resp.text()?;
    let text_value = JsFuture::from(text_promise).await?;

    Ok(text_value.as_string().unwrap_or_default())
}

/// 使用 Fetch API 获取 JSON 数据
///
/// # 参数
/// - `url`: 要请求的 URL
///
/// # 返回值
/// 返回 Promise，成功时包含 JSON 对象，失败时包含错误信息
///
/// # 示例
/// ```javascript
/// const data = await fetch_json('https://api.example.com/users');
/// console.log(data);
/// ```
#[wasm_bindgen]
pub async fn fetch_json(url: String) -> Result<JsValue, JsValue> {
    let opts = RequestInit::new();
    opts.set_method("GET");
    opts.set_mode(RequestMode::Cors);

    let request = Request::new_with_str(&url)?;

    let window = web_sys::window().ok_or_else(|| JsValue::from_str("No window object"))?;
    let resp_value = JsFuture::from(window.fetch_with_request(&request)).await?;
    let resp: Response = resp_value.dyn_into()?;

    if !resp.ok() {
        return Err(JsValue::from_str(&format!("HTTP error: {}", resp.status())));
    }

    let json_promise = resp.json()?;
    let json_value = JsFuture::from(json_promise).await?;

    Ok(json_value)
}

/// POST 请求示例
///
/// # 参数
/// - `url`: 要请求的 URL
/// - `body`: 请求体内容
///
/// # 返回值
/// 返回 Promise，成功时包含响应文本
#[wasm_bindgen]
pub async fn post_data(url: String, body: String) -> Result<String, JsValue> {
    let opts = RequestInit::new();
    opts.set_method("POST");
    opts.set_mode(RequestMode::Cors);
    opts.set_body(&JsValue::from_str(&body));

    let request = Request::new_with_str(&url)?;

    // 设置 Content-Type header
    request.headers().set("Content-Type", "application/json")?;

    let window = web_sys::window().ok_or_else(|| JsValue::from_str("No window object"))?;
    let resp_value = JsFuture::from(window.fetch_with_request(&request)).await?;
    let resp: Response = resp_value.dyn_into()?;

    if !resp.ok() {
        return Err(JsValue::from_str(&format!("HTTP error: {}", resp.status())));
    }

    let text_promise = resp.text()?;
    let text_value = JsFuture::from(text_promise).await?;

    Ok(text_value.as_string().unwrap_or_default())
}

#[wasm_bindgen(start)]
#[allow(clippy::main_recursion)]
pub fn main() {
    #[cfg(target_arch = "wasm32")]
    {
        use web_sys::console;
        console::log_1(&"Async fetch example loaded!".into());
        console::log_1(&"Use fetch_text(url) or fetch_json(url) from JavaScript".into());
    }
}
