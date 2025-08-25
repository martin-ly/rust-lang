//! 内存优化实践示例

use std::collections::VecDeque;

/// 简单对象池实现
pub struct ObjectPool<T> {
    objects: VecDeque<T>,
    factory: Box<dyn Fn() -> T>,
}

impl<T> ObjectPool<T> {
    pub fn new<F>(factory: F) -> Self 
    where
        F: Fn() -> T + 'static,
    {
        Self {
            objects: VecDeque::new(),
            factory: Box::new(factory),
        }
    }

    pub fn acquire(&mut self) -> T {
        self.objects.pop_front().unwrap_or_else(|| (self.factory)())
    }

    pub fn release(&mut self, obj: T) {
        self.objects.push_back(obj);
    }
}

/// 零拷贝缓冲区
pub struct ZeroCopyBuffer {
    data: Vec<u8>,
    read_pos: usize,
    write_pos: usize,
}

impl ZeroCopyBuffer {
    pub fn new(capacity: usize) -> Self {
        Self {
            data: vec![0; capacity],
            read_pos: 0,
            write_pos: 0,
        }
    }

    pub fn write(&mut self, data: &[u8]) -> usize {
        let available = self.data.len() - self.write_pos;
        let to_write = data.len().min(available);
        
        if to_write > 0 {
            self.data[self.write_pos..self.write_pos + to_write].copy_from_slice(&data[..to_write]);
            self.write_pos += to_write;
        }
        
        to_write
    }

    pub fn read(&mut self, buffer: &mut [u8]) -> usize {
        let available = self.write_pos - self.read_pos;
        let to_read = buffer.len().min(available);
        
        if to_read > 0 {
            buffer[..to_read].copy_from_slice(&self.data[self.read_pos..self.read_pos + to_read]);
            self.read_pos += to_read;
        }
        
        to_read
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_object_pool() {
        let mut pool = ObjectPool::new(|| String::from("test"));
        
        let obj1 = pool.acquire();
        let obj2 = pool.acquire();
        
        assert_eq!(obj1, "test");
        assert_eq!(obj2, "test");
        
        pool.release(obj1);
        pool.release(obj2);
    }

    #[test]
    fn test_zero_copy_buffer() {
        let mut buffer = ZeroCopyBuffer::new(100);
        let test_data = b"Hello";
        
        let written = buffer.write(test_data);
        assert_eq!(written, 5);
        
        let mut read_buffer = [0u8; 5];
        let read = buffer.read(&mut read_buffer);
        assert_eq!(read, 5);
        assert_eq!(&read_buffer, test_data);
    }
}
