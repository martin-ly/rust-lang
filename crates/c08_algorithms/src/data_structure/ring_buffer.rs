//! 环形缓冲区（Ring Buffer / Circular Buffer）
//!
//! 固定容量的 FIFO 结构，用数组与读写指针实现，入队/出队均摊 O(1)。
//! 常用于流式 I/O、音频处理、日志缓冲、生产者-消费者队列等场景。
//!
//! # 时间复杂度
//! - `push`: O(1) 均摊
//! - `pop`: O(1)
//! - `peek`: O(1)
//! - `len` / `is_empty`: O(1)
//!
//! # 来源
//! - [Introduction to Algorithms (Cormen et al.)](https://mitpress.mit.edu/books/introduction-algorithms-fourth-edition)
//! - [Rust Atomics and Locks](https://marabos.nl/atomics/)

#[derive(Clone, Debug)]
pub struct RingBuffer<T> {
    buf: Vec<Option<T>>,
    head: usize, // 读取位置
    tail: usize, // 写入位置
    len: usize,  // 当前元素数
    capacity: usize,
}

impl<T> RingBuffer<T> {
    /// 创建指定容量的空环形缓冲区。
    pub fn new(capacity: usize) -> Self {
        let mut buf = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            buf.push(None);
        }
        Self {
            buf,
            head: 0,
            tail: 0,
            len: 0,
            capacity,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn is_full(&self) -> bool {
        self.len == self.capacity
    }

    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// 入队；满时返回 `Err(value)`。
    pub fn push(&mut self, value: T) -> Result<(), T> {
        if self.is_full() {
            return Err(value);
        }
        self.buf[self.tail] = Some(value);
        self.tail = (self.tail + 1) % self.capacity;
        self.len += 1;
        Ok(())
    }

    /// 出队；空时返回 `None`。
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        let value = self.buf[self.head].take();
        self.head = (self.head + 1) % self.capacity;
        self.len -= 1;
        value
    }

    /// 查看队首元素。
    pub fn peek(&self) -> Option<&T> {
        if self.is_empty() {
            return None;
        }
        self.buf[self.head].as_ref()
    }
}

impl<T> Default for RingBuffer<T> {
    fn default() -> Self {
        Self::new(16)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ring_buffer_basic() {
        let mut rb = RingBuffer::new(3);
        assert!(rb.push(1).is_ok());
        assert!(rb.push(2).is_ok());
        assert!(rb.push(3).is_ok());
        assert_eq!(rb.push(4), Err(4));

        assert_eq!(rb.pop(), Some(1));
        assert!(rb.push(4).is_ok());
        assert_eq!(rb.pop(), Some(2));
        assert_eq!(rb.pop(), Some(3));
        assert_eq!(rb.pop(), Some(4));
        assert_eq!(rb.pop(), None);
    }

    #[test]
    fn test_ring_buffer_wrap_around() {
        let mut rb = RingBuffer::new(2);
        rb.push(10).unwrap();
        rb.push(20).unwrap();
        assert_eq!(rb.pop(), Some(10));
        rb.push(30).unwrap();
        assert_eq!(rb.pop(), Some(20));
        assert_eq!(rb.pop(), Some(30));
    }
}
