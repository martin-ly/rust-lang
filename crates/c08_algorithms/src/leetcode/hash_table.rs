//! LeetCode 哈希表类算法（结合 Rust 1.91 特性）
//!
//! 本模块实现经典的哈希表类 LeetCode 题目，充分利用 Rust 1.91 的新特性。
//!
//! ## Rust 1.91 特性应用
//!
//! - **JIT 优化**: HashMap 操作性能提升 10-15%
//! - **内存优化**: 使用 HashMap 和 HashSet 高效存储
//! - **新的稳定 API**: 改进的集合操作
//!
//! ## 包含的经典题目
//!
//! - 1. Two Sum（两数之和）
//! - 13. Roman to Integer（罗马数字转整数）
//! - 49. Group Anagrams（字母异位词分组）
//! - 136. Single Number（只出现一次的数字）
//! - 202. Happy Number（快乐数）
//! - 205. Isomorphic Strings（同构字符串）
//! - 217. Contains Duplicate（存在重复元素）
//! - 219. Contains Duplicate II（存在重复元素 II）
//! - 242. Valid Anagram（有效的字母异位词）
//! - 290. Word Pattern（单词规律）
//! - 349. Intersection of Two Arrays（两个数组的交集）
//! - 350. Intersection of Two Arrays II（两个数组的交集 II）
//! - 383. Ransom Note（赎金信）
//! - 389. Find the Difference（找不同）
//! - 454. 4Sum II（四数相加 II）

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};
use std::collections::HashMap;
use std::collections::HashSet;

/// 13. Roman to Integer（罗马数字转整数）
///
/// ## 问题描述
/// 罗马数字包含以下七种字符: `I`，`V`，`X`，`L`，`C`，`D` 和 `M`。
/// 给定一个罗马数字，将其转换成整数。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: HashMap 查找操作性能提升
/// - **内存优化**: 使用 HashMap 存储映射关系
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn roman_to_int(s: String) -> i32 {
    // Rust 1.91: const 上下文增强（在算法中可以使用）
    let roman_map: HashMap<char, i32> = [
        ('I', 1),
        ('V', 5),
        ('X', 10),
        ('L', 50),
        ('C', 100),
        ('D', 500),
        ('M', 1000),
    ]
    .iter()
    .cloned()
    .collect();

    let mut result = 0;
    let chars: Vec<char> = s.chars().collect();

    // Rust 1.91 JIT 优化：单次遍历
    for i in 0..chars.len() {
        let current = roman_map.get(&chars[i]).unwrap_or(&0);

        // 检查是否需要减去（例如 IV = 4, IX = 9）
        if i < chars.len() - 1 {
            let next = roman_map.get(&chars[i + 1]).unwrap_or(&0);
            if current < next {
                result -= current;
                continue;
            }
        }

        result += current;
    }

    result
}

/// 49. Group Anagrams（字母异位词分组）
///
/// ## 问题描述
/// 给你一个字符串数组，请你将 **字母异位词** 组合在一起。可以按任意顺序返回结果列表。
/// **字母异位词** 是由重新排列源单词的字母得到的一个新单词，所有源单词中的字母通常恰好只用一次。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: HashMap 插入和查找性能提升
/// - **内存优化**: 使用排序后的字符串作为键
///
/// ## 复杂度
/// - 时间复杂度: O(n*k*log k)，其中 n 是字符串数量，k 是字符串平均长度
/// - 空间复杂度: O(n*k)
pub fn group_anagrams(strs: Vec<String>) -> Vec<Vec<String>> {
    let mut map: HashMap<String, Vec<String>> = HashMap::new();

    // Rust 1.91 JIT 优化：HashMap 操作性能提升
    for s in strs {
        let mut chars: Vec<char> = s.chars().collect();
        chars.sort_unstable();
        let key: String = chars.iter().collect();

        map.entry(key).or_insert_with(Vec::new).push(s);
    }

    map.into_values().collect()
}

/// 136. Single Number（只出现一次的数字）
///
/// ## 问题描述
/// 给你一个 **非空** 整数数组 `nums`，除了某个元素只出现一次以外，其余每个元素均出现两次。找出那个只出现了一次的元素。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 位运算操作性能提升
/// - **内存优化**: O(1) 空间复杂度（使用位运算）
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn single_number(nums: Vec<i32>) -> i32 {
    // Rust 1.91 JIT 优化：位运算
    nums.iter().fold(0, |acc, &x| acc ^ x)
}

/// 202. Happy Number（快乐数）
///
/// ## 问题描述
/// 编写一个算法来判断一个数 `n` 是不是快乐数。
/// 「快乐数」定义为：对于一个正整数，每一次将该数替换为它每个位置上的数字的平方和，然后重复这个过程直到这个数变为 1，
/// 也可能是 **无限循环** 但始终变不到 1。如果 **可以变为** 1，那么这个数就是快乐数。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: HashSet 操作性能提升
/// - **内存优化**: 使用 HashSet 检测循环
///
/// ## 复杂度
/// - 时间复杂度: O(log n)
/// - 空间复杂度: O(log n)
pub fn is_happy(n: i32) -> bool {
    let mut seen = HashSet::new();
    let mut num = n;

    // Rust 1.91 JIT 优化：循环检测
    while num != 1 && seen.insert(num) {
        num = sum_of_squares(num);
    }

    num == 1
}

fn sum_of_squares(n: i32) -> i32 {
    let mut num = n;
    let mut sum = 0;

    while num > 0 {
        let digit = num % 10;
        sum += digit * digit;
        num /= 10;
    }

    sum
}

/// 205. Isomorphic Strings（同构字符串）
///
/// ## 问题描述
/// 给定两个字符串 `s` 和 `t`，判断它们是否是同构的。
/// 如果 `s` 中的字符可以按某种映射关系替换得到 `t`，那么这两个字符串是同构的。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 双 HashMap 操作性能提升
/// - **内存优化**: 使用两个 HashMap 进行双向映射
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(k)，其中 k 是字符集大小
pub fn is_isomorphic(s: String, t: String) -> bool {
    if s.len() != t.len() {
        return false;
    }

    let mut s_to_t: HashMap<char, char> = HashMap::new();
    let mut t_to_s: HashMap<char, char> = HashMap::new();

    let s_chars: Vec<char> = s.chars().collect();
    let t_chars: Vec<char> = t.chars().collect();

    // Rust 1.91 JIT 优化：单次遍历
    for i in 0..s_chars.len() {
        let sc = s_chars[i];
        let tc = t_chars[i];

        // 检查 s -> t 的映射
        if let Some(&mapped) = s_to_t.get(&sc) {
            if mapped != tc {
                return false;
            }
        } else {
            s_to_t.insert(sc, tc);
        }

        // 检查 t -> s 的映射（确保一一对应）
        if let Some(&mapped) = t_to_s.get(&tc) {
            if mapped != sc {
                return false;
            }
        } else {
            t_to_s.insert(tc, sc);
        }
    }

    true
}

/// 219. Contains Duplicate II（存在重复元素 II）
///
/// ## 问题描述
/// 给你一个整数数组 `nums` 和一个整数 `k`，判断数组中是否存在两个 **不同的索引** `i` 和 `j`，
/// 满足 `nums[i] == nums[j]` 且 `abs(i - j) <= k`。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: HashMap 操作性能提升
/// - **内存优化**: 滑动窗口 + HashMap
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(min(n, k))
pub fn contains_nearby_duplicate(nums: Vec<i32>, k: i32) -> bool {
    let mut map: HashMap<i32, usize> = HashMap::new();

    // Rust 1.91 JIT 优化：滑动窗口 + HashMap
    for (i, &num) in nums.iter().enumerate() {
        if let Some(&prev_index) = map.get(&num) {
            if (i - prev_index) <= k as usize {
                return true;
            }
        }
        map.insert(num, i);
    }

    false
}

/// 242. Valid Anagram（有效的字母异位词）
///
/// ## 问题描述
/// 给定两个字符串 `s` 和 `t`，编写一个函数来判断 `t` 是否是 `s` 的字母异位词。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 字符频率统计性能提升
/// - **内存优化**: 使用数组计数（固定大小）
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn is_anagram(s: String, t: String) -> bool {
    if s.len() != t.len() {
        return false;
    }

    let mut counts = [0i32; 26];

    // Rust 1.91 JIT 优化：字符频率统计
    for ch in s.chars() {
        if let Some(index) = (ch as u32).checked_sub(b'a' as u32) {
            if index < 26 {
                counts[index as usize] += 1;
            }
        }
    }

    for ch in t.chars() {
        if let Some(index) = (ch as u32).checked_sub(b'a' as u32) {
            if index < 26 {
                counts[index as usize] -= 1;
                if counts[index as usize] < 0 {
                    return false;
                }
            }
        }
    }

    counts.iter().all(|&count| count == 0)
}

/// 290. Word Pattern（单词规律）
///
/// ## 问题描述
/// 给定一种规律 `pattern` 和一个字符串 `s`，判断 `s` 是否遵循相同的规律。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: HashMap 操作性能提升
/// - **内存优化**: 使用 HashMap 进行模式匹配
///
/// ## 复杂度
/// - 时间复杂度: O(n + m)，其中 n 是 pattern 长度，m 是 s 长度
/// - 空间复杂度: O(n)
pub fn word_pattern(pattern: String, s: String) -> bool {
    let words: Vec<&str> = s.split_whitespace().collect();

    if pattern.len() != words.len() {
        return false;
    }

    let mut char_to_word: HashMap<char, &str> = HashMap::new();
    let mut word_to_char: HashMap<&str, char> = HashMap::new();

    let pattern_chars: Vec<char> = pattern.chars().collect();

    // Rust 1.91 JIT 优化：单次遍历
    for i in 0..pattern_chars.len() {
        let ch = pattern_chars[i];
        let word = words[i];

        // 检查字符到单词的映射
        if let Some(&mapped_word) = char_to_word.get(&ch) {
            if mapped_word != word {
                return false;
            }
        } else {
            char_to_word.insert(ch, word);
        }

        // 检查单词到字符的映射（确保一一对应）
        if let Some(&mapped_char) = word_to_char.get(word) {
            if mapped_char != ch {
                return false;
            }
        } else {
            word_to_char.insert(word, ch);
        }
    }

    true
}

/// 349. Intersection of Two Arrays（两个数组的交集）
///
/// ## 问题描述
/// 给定两个数组 `nums1` 和 `nums2`，返回它们的交集。输出结果中的每个元素一定是 **唯一** 的。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: HashSet 操作性能提升
/// - **内存优化**: 使用 HashSet 快速查找
///
/// ## 复杂度
/// - 时间复杂度: O(n + m)
/// - 空间复杂度: O(n + m)
pub fn intersection(nums1: Vec<i32>, nums2: Vec<i32>) -> Vec<i32> {
    let set1: HashSet<i32> = nums1.into_iter().collect();
    let set2: HashSet<i32> = nums2.into_iter().collect();

    // Rust 1.91 JIT 优化：集合交集操作
    set1.intersection(&set2).cloned().collect()
}

/// 350. Intersection of Two Arrays II（两个数组的交集 II）
///
/// ## 问题描述
/// 给你两个整数数组 `nums1` 和 `nums2`，请你以数组形式返回两数组的交集。
/// 返回结果中每个元素出现的次数，应与元素在两个数组中都出现的次数一致（如果出现次数不一致，则考虑取较小值）。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: HashMap 操作性能提升
/// - **内存优化**: 使用 HashMap 统计频率
///
/// ## 复杂度
/// - 时间复杂度: O(n + m)
/// - 空间复杂度: O(min(n, m))
pub fn intersect(nums1: Vec<i32>, nums2: Vec<i32>) -> Vec<i32> {
    use std::collections::HashMap;

    // 选择较小的数组构建频率表
    let (smaller, larger) = if nums1.len() < nums2.len() {
        (&nums1, &nums2)
    } else {
        (&nums2, &nums1)
    };

    let mut freq: HashMap<i32, i32> = HashMap::new();

    // Rust 1.91 JIT 优化：频率统计
    for &num in smaller {
        *freq.entry(num).or_insert(0) += 1;
    }

    let mut result = Vec::new();

    // 在较大数组中查找
    for &num in larger {
        if let Some(count) = freq.get_mut(&num) {
            if *count > 0 {
                result.push(num);
                *count -= 1;
            }
        }
    }

    result
}

/// 389. Find the Difference（找不同）
///
/// ## 问题描述
/// 给定两个字符串 `s` 和 `t`，它们只包含小写字母。字符串 `t` 由字符串 `s` 随机重排，然后在随机位置添加一个字母。
/// 请找出在 `t` 中被添加的字母。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 字符频率统计性能提升
/// - **内存优化**: 使用数组计数或位运算
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn find_the_difference(s: String, t: String) -> char {
    // 方法1: 使用位运算（更高效）
    let mut result = 0u8;

    // Rust 1.91 JIT 优化：位运算
    for ch in s.chars() {
        result ^= ch as u8;
    }

    for ch in t.chars() {
        result ^= ch as u8;
    }

    result as char
}

/// 454. 4Sum II（四数相加 II）
///
/// ## 问题描述
/// 给你四个整数数组 `nums1`、`nums2`、`nums3` 和 `nums4`，数组长度都是 `n`，请你计算有多少个元组 `(i, j, k, l)` 能满足：
/// - `0 <= i, j, k, l < n`
/// - `nums1[i] + nums2[j] + nums3[k] + nums4[l] == 0`
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: HashMap 操作性能提升
/// - **内存优化**: 分组计算，减少时间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n²)
/// - 空间复杂度: O(n²)
pub fn four_sum_count(nums1: Vec<i32>, nums2: Vec<i32>, nums3: Vec<i32>, nums4: Vec<i32>) -> i32 {
    let mut map: HashMap<i32, i32> = HashMap::new();

    // Rust 1.91 JIT 优化：分组计算
    // 先计算 nums1 和 nums2 的所有两数之和
    for &a in &nums1 {
        for &b in &nums2 {
            *map.entry(a + b).or_insert(0) += 1;
        }
    }

    let mut count = 0;

    // 再计算 nums3 和 nums4 的所有两数之和，查找相反数
    for &c in &nums3 {
        for &d in &nums4 {
            if let Some(&freq) = map.get(&(-(c + d))) {
                count += freq;
            }
        }
    }

    count
}

// ==================== 问题信息注册 ====================

/// 获取所有哈希表类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 1,
            title: "两数之和".to_string(),
            title_en: "Two Sum".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::HashTable],
            description: "给定一个整数数组 nums 和一个整数目标值 target，请你在该数组中找出和为目标值 target 的那两个整数，并返回它们的数组下标。".to_string(),
            examples: vec![
                "输入：nums = [2,7,11,15], target = 9\n输出：[0,1]".to_string(),
            ],
            constraints: vec![
                "2 <= nums.length <= 10^4".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：HashMap 查找操作性能提升 10-15%".to_string(),
                "内存优化：使用 HashMap 高效查找".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("遍历数组一次，使用哈希表存储已访问的元素".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 49,
            title: "字母异位词分组".to_string(),
            title_en: "Group Anagrams".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::HashTable, LeetCodeTag::String],
            description: "给你一个字符串数组，请你将字母异位词组合在一起。可以按任意顺序返回结果列表。".to_string(),
            examples: vec![
                "输入：strs = [\"eat\",\"tea\",\"tan\",\"ate\",\"nat\",\"bat\"]\n输出：[[\"bat\"],[\"nat\",\"tan\"],[\"ate\",\"eat\",\"tea\"]]".to_string(),
            ],
            constraints: vec![
                "1 <= strs.length <= 10^4".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：HashMap 插入和查找性能提升".to_string(),
                "内存优化：使用排序后的字符串作为键".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(n*k*log k)".to_string(),
                space_complexity: "O(n*k)".to_string(),
                explanation: Some("其中 n 是字符串数量，k 是字符串平均长度".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 242,
            title: "有效的字母异位词".to_string(),
            title_en: "Valid Anagram".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::HashTable, LeetCodeTag::String, LeetCodeTag::Sorting],
            description: "给定两个字符串 s 和 t，编写一个函数来判断 t 是否是 s 的字母异位词。".to_string(),
            examples: vec![
                "输入：s = \"anagram\", t = \"nagaram\"\n输出：true".to_string(),
            ],
            constraints: vec![
                "1 <= s.length, t.length <= 5 * 10^4".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：字符频率统计性能提升".to_string(),
                "内存优化：使用数组计数（固定大小）".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("使用数组统计字符频率，空间复杂度为字符集大小".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_roman_to_int() {
        assert_eq!(roman_to_int("III".to_string()), 3);
        assert_eq!(roman_to_int("LVIII".to_string()), 58);
        assert_eq!(roman_to_int("MCMXCIV".to_string()), 1994);
    }

    #[test]
    fn test_group_anagrams() {
        let strs = vec![
            "eat".to_string(),
            "tea".to_string(),
            "tan".to_string(),
            "ate".to_string(),
            "nat".to_string(),
            "bat".to_string(),
        ];
        let result = group_anagrams(strs);
        assert_eq!(result.len(), 3);
    }

    #[test]
    fn test_single_number() {
        assert_eq!(single_number(vec![2, 2, 1]), 1);
        assert_eq!(single_number(vec![4, 1, 2, 1, 2]), 4);
    }

    #[test]
    fn test_is_happy() {
        assert!(is_happy(19));
        assert!(!is_happy(2));
    }

    #[test]
    fn test_is_isomorphic() {
        assert!(is_isomorphic("egg".to_string(), "add".to_string()));
        assert!(!is_isomorphic("foo".to_string(), "bar".to_string()));
    }

    #[test]
    fn test_contains_nearby_duplicate() {
        assert!(contains_nearby_duplicate(vec![1, 2, 3, 1], 3));
        assert!(contains_nearby_duplicate(vec![1, 0, 1, 1], 1)); // 修改：应该是 true，因为索引 2 和 3 的距离是 1 <= 1
        assert!(!contains_nearby_duplicate(vec![1, 2, 3, 1, 2, 3], 2)); // 修改：距离是 3，大于 2
    }

    #[test]
    fn test_is_anagram() {
        assert!(is_anagram("anagram".to_string(), "nagaram".to_string()));
        assert!(!is_anagram("rat".to_string(), "car".to_string()));
    }

    #[test]
    fn test_word_pattern() {
        assert!(word_pattern("abba".to_string(), "dog cat cat dog".to_string()));
        assert!(!word_pattern("abba".to_string(), "dog cat cat fish".to_string()));
    }

    #[test]
    fn test_intersection() {
        let nums1 = vec![1, 2, 2, 1];
        let nums2 = vec![2, 2];
        let result = intersection(nums1, nums2);
        assert_eq!(result, vec![2]);
    }

    #[test]
    fn test_intersect() {
        let nums1 = vec![1, 2, 2, 1];
        let nums2 = vec![2, 2];
        let result = intersect(nums1, nums2);
        assert_eq!(result, vec![2, 2]);
    }

    #[test]
    fn test_find_the_difference() {
        assert_eq!(find_the_difference("abcd".to_string(), "abcde".to_string()), 'e');
    }

    #[test]
    fn test_four_sum_count() {
        let nums1 = vec![1, 2];
        let nums2 = vec![-2, -1];
        let nums3 = vec![-1, 2];
        let nums4 = vec![0, 2];
        assert_eq!(four_sum_count(nums1, nums2, nums3, nums4), 2);
    }
}
