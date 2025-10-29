// trait多态与形式化验证示例
// 工程意义：演示Rust trait多态与接口安全的形式化建模，适用于Creusot/Prusti等工具验证

trait Summary {
    fn summarize(&self) -> String;
}

struct NewsArticle {
    headline: String,
    author: String,
}

impl Summary for NewsArticle {
    fn summarize(&self) -> String {
        format!("{}, by {}", self.headline, self.author)
    }
}

fn notify(item: &impl Summary) -> String {
    // 前置条件：item实现了Summary trait
    // 后置条件：返回非空字符串
    let s = item.summarize();
    assert!(!s.is_empty());
    s
}

fn main() {
    let article = NewsArticle {
        headline: String::from("Rust 1.70 Released!"),
        author: String::from("Rustacean"),
    };
    let summary = notify(&article);
    println!("{}", summary);
}

// 形式化注释：
// ∀T: Summary, ∀item: &T, notify(item) ≠ ""
// 工具建议：Creusot/Prusti 可验证trait多态接口安全 