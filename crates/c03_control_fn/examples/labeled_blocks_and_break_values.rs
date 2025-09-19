fn find_first_even(nums: &[i32]) -> Option<i32> {
    'out: loop {
        for &n in nums {
            if n % 2 == 0 { break 'out Some(n); }
        }
        break 'out None;
    }
}

fn index_of(hay: &[i32], needle: i32) -> Option<usize> {
    let res = 'search: loop {
        for (i, &x) in hay.iter().enumerate() {
            if x == needle { break 'search Some(i); }
        }
        break 'search None;
    };
    res
}

fn compute() -> i32 {
    'blk: {
        if 1 + 1 == 2 { break 'blk 10; }
        0
    }
}

fn main() {
    assert_eq!(find_first_even(&[1,3,4,5]), Some(4));
    assert_eq!(index_of(&[10,20,30], 20), Some(1));
    assert_eq!(compute(), 10);
}


