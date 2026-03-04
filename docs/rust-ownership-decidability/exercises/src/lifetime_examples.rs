//! Lifetime Examples
//!
//! Demonstrates explicit lifetime annotations and elision rules.

/// Example 1: Explicit Lifetime Annotation
/// 
/// The returned reference has the same lifetime as the inputs.
/// ```
/// use rust_ownership_decidability::lifetime_examples::longest;
/// let s1 = String::from("longer string");
/// let s2 = "short";
/// let result = longest(&s1, s2);
/// assert_eq!(result, "longer string");
/// ```
pub fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

/// Example 2: Struct with Lifetime
/// 
/// A struct that holds a reference.
#[derive(Debug)]
pub struct ImportantExcerpt<'a> {
    pub part: &'a str,
}

impl<'a> ImportantExcerpt<'a> {
    /// Returns the stored reference
    pub fn part(&self) -> &str {
        self.part
    }
    
    /// Compare with another excerpt
    pub fn compare(&self, other: &'a str) -> &'a str {
        if self.part.len() > other.len() {
            self.part
        } else {
            other
        }
    }
}

/// Example 3: Lifetime Elision
/// 
/// The compiler can infer simple lifetime patterns.
pub fn first_word_elided(s: &str) -> &str {
    let bytes = s.as_bytes();
    for (i, &item) in bytes.iter().enumerate() {
        if item == b' ' {
            return &s[0..i];
        }
    }
    &s[..]
}

/// Example 4: Static Lifetime
/// 
/// Static lifetime lasts for the entire program duration.
pub fn get_static_string() -> &'static str {
    "I live forever!"
}

/// Example 5: Multiple Lifetimes
/// 
/// Different references can have different lifetimes.
pub fn mix_lifetimes<'a, 'b>(x: &'a str, _y: &'b str) -> &'a str {
    x // Only x's lifetime matters for return
}

/// Example 6: Lifetime Bounds
/// 
/// T: 'a means T outlives 'a.
pub struct Wrapper<'a, T: 'a> {
    data: &'a T,
}

impl<'a, T> Wrapper<'a, T> {
    pub fn new(data: &'a T) -> Self {
        Wrapper { data }
    }
    
    pub fn get(&self) -> &T {
        self.data
    }
}

/// Example 7: Lifetime in Trait
/// 
/// Traits can have lifetime parameters too.
pub trait Parser<'a> {
    fn parse(&self, input: &'a str) -> Option<&'a str>;
}

pub struct WordParser;

impl<'a> Parser<'a> for WordParser {
    fn parse(&self, input: &'a str) -> Option<&'a str> {
        input.split_whitespace().next()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_longest() {
        let s1 = String::from("longer string");
        let s2 = "short";
        assert_eq!(longest(&s1, s2), "longer string");
    }

    #[test]
    fn test_struct_lifetime() {
        let text = String::from("hello world");
        let excerpt = ImportantExcerpt { part: &text[0..5] };
        assert_eq!(excerpt.part(), "hello");
    }

    #[test]
    fn test_first_word() {
        let s = "hello world";
        assert_eq!(first_word_elided(s), "hello");
    }

    #[test]
    fn test_static_lifetime() {
        let s = get_static_string();
        assert_eq!(s, "I live forever!");
    }

    #[test]
    fn test_wrapper() {
        let data = 42;
        let wrapper = Wrapper::new(&data);
        assert_eq!(*wrapper.get(), 42);
    }

    #[test]
    fn test_parser() {
        let parser = WordParser;
        assert_eq!(parser.parse("hello world"), Some("hello"));
    }
}
