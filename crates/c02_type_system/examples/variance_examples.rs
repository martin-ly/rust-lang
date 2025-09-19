//! 变型（Variance）、GATs 与 HRTB 示例

// 1) 变型直觉示例
fn covariant_ref<'short, 'long: 'short>(r: &'long str) -> &'short str { r }

// 2) GATs：在 trait 中定义依赖生命周期的关联类型
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

// 3) HRTB：对任意生命周期的函数/闭包
fn total_len_for_all<F>(mut next: F) -> usize
where
    F: for<'a> FnMut(&'a str) -> Option<&'a str>,
{
    let mut sum = 0;
    while let Some(s) = next("dummy") { sum += s.len(); }
    sum
}

fn main() {
    // 变型直觉：长 -> 短（协变）
    let long: &'static str = "hello";
    let _short: &str = covariant_ref(long);

    // GATs 流式迭代
    let mut lines = Lines { data: "a\nbc\n", pos: 0 };
    while let Some(line) = lines.next() { println!("line: {}", line); }

    // HRTB
    let data = ["a", "bb", "ccc"]; let mut i = 0;
    let s = total_len_for_all(|_| { if i < data.len() { let r = Some(data[i]); i += 1; r } else { None } });
    println!("sum = {}", s);
}


