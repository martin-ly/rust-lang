#[allow(dead_code)]
pub trait Parser<'a> {
    fn parse(&self, input: &'a str) -> impl Iterator<Item = &'a str> + use<'a, Self>;
}

pub struct WordParser;
impl<'a> Parser<'a> for WordParser {
    fn parse(&self, input: &'a str) -> impl Iterator<Item = &'a str> + use<'a> {
        input.split_whitespace()
    }
}
