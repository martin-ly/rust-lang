//! 最小 Leptos 计数器组件示例。
//!
//! 本示例展示 Leptos 0.8 的细粒度响应式信号与 `view!` 宏。在真实 SSR/CSR
//! 应用中，会由 `leptos_axum` 或浏览器渲染；此处为最小可检查示例。

use leptos::prelude::*;

/// 计数器组件，使用局部响应式信号。
#[component]
fn Counter() -> impl IntoView {
    let (count, set_count) = signal(0);

    view! {
        <div>
            <button on:click=move |_| set_count.update(|n| *n -= 1)>
                "-"
            </button>
            <span>{count}</span>
            <button on:click=move |_| set_count.update(|n| *n += 1)>
                "+"
            </button>
        </div>
    }
}

fn main() {
    // 仅展示组件定义，不实际挂载到 DOM。
    println!("Leptos counter example defined (not mounting).");
}
