//! # Brown University CRP Ownership Inventory — Program 04
//!
//! **EN**: Lifetime Annotations
//! **Summary**: Explicitly annotate lifetimes for structs and functions that hold references,
//! ensuring references never outlive the data they point to.
//! **Key Terms**: 生命周期 (lifetime), 生命周期参数 (lifetime parameter), 生命周期省略
//! (lifetime elision), 结构体借用 (struct references), 引用 (reference), 借用字段
//! (borrowed field).
//! **Related Concepts**:
//! [`concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`](../../../../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md),
//! [`concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md`](../../../../../concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md),
//! [`concept/01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md`](../../../../../concept/01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md).
//!
//! **来源 / Source**: Brown University CRP Ownership Inventory 样题
//! **主题 / Topic**: 生命周期标注 / Lifetime Annotations
//!
//! ## 学习目标 / Learning Goal
//!
//! 为包含引用的结构体和函数显式标注生命周期，确保引用不会比被引用数据活得更久。
//! Explicitly annotate lifetimes for structs and functions that hold references,
//! ensuring references never outlive the data they point to.
//!
//! ## TODO / Tasks
//!
//! 1. 为 `BookReview` 结构体添加生命周期参数。
//!    Add lifetime parameters to the `BookReview` struct.
//! 2. 为 `longer_review` 函数添加生命周期参数，使其返回两个 `BookReview` 中较长的评论引用。
//!    Add lifetime parameters to `longer_review` so it returns a reference to the longer review.
//! 3. 解释为什么 `BookReview<'a>` 必须和 `&'a str` 绑定相同的生命周期。
//!    Explain why `BookReview<'a>` must tie its lifetime to that of `&'a str`.

/// 图书评论：包含书名（owned）和评论文本（借用）。
/// Book review: contains an owned title and a borrowed review text.
///
/// TODO: 添加生命周期参数，使 `review` 字段合法。
/// TODO: Add lifetime parameters so the `review` field is valid.
pub struct BookReview<'a> {
    pub title: String,
    pub review: &'a str,
}

/// 返回两个评论中较长的那个引用。
/// Returns a reference to the longer of two reviews.
///
/// TODO: 为输入输出引用标注生命周期。
/// TODO: Annotate lifetimes for the input and output references.
pub fn longer_review<'a>(a: &'a BookReview<'a>, b: &'a BookReview<'a>) -> &'a str {
    if a.review.len() >= b.review.len() {
        a.review
    } else {
        b.review
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_longer_review() {
        let review_text_a = "A great introduction to Rust.";
        let review_text_b = "Detailed but a bit long for beginners.";

        let book_a = BookReview {
            title: String::from("Rust Book"),
            review: review_text_a,
        };
        let book_b = BookReview {
            title: String::from("Rust Reference"),
            review: review_text_b,
        };

        let chosen = longer_review(&book_a, &book_b);
        assert_eq!(chosen, review_text_b);
    }
}
