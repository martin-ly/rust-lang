fn find_first_even(nums: &[i32]) -> Option<i32> {
    for &n in nums {
        if n % 2 == 0 { return Some(n); }
    }
    None
}

fn index_of(hay: &[i32], needle: i32) -> Option<usize> {
    for (i, &x) in hay.iter().enumerate() {
        if x == needle { return Some(i); }
    }
    None
}

fn compute() -> i32 {
    'blk: {
        if true { break 'blk 10; }
        0
    }
}

fn main() {
    assert_eq!(find_first_even(&[1,3,4,5]), Some(4));
    assert_eq!(index_of(&[10,20,30], 20), Some(1));
    assert_eq!(compute(), 10);
}
