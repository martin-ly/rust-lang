trait StreamingIter {
    type Item<'a>
    where
        Self: 'a;
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

struct Lines<'s> { data: &'s str, pos: usize }

impl<'s> StreamingIter for Lines<'s> {
    type Item<'a> = &'a str where Self: 'a;
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>> {
        if self.pos >= self.data.len() { return None; }
        let bytes = self.data.as_bytes();
        let start = self.pos;
        while self.pos < bytes.len() && bytes[self.pos] != b'\n' { self.pos += 1; }
        let end = self.pos;
        if self.pos < bytes.len() { self.pos += 1; }
        Some(&self.data[start..end])
    }
}

#[test]
fn test_lines_gats() {
    let mut lines = Lines { data: "a\nbc\n", pos: 0 };
    assert_eq!(lines.next(), Some("a"));
    assert_eq!(lines.next(), Some("bc"));
    assert_eq!(lines.next(), None);
}


