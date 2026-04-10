//! 关联类型测试
//!
//! 测试Rust的关联类型系统：
//! - 基本关联类型
//! - 泛型关联类型 (GATs)
//! - 关联常量
//! - 关联类型约束

/// 测试基本关联类型
#[test]
fn test_basic_associated_types() {
    trait Iterator {
        type Item;

        fn next(&mut self) -> Option<Self::Item>;
    }

    struct Counter {
        count: u32,
    }

    impl Iterator for Counter {
        type Item = u32;

        fn next(&mut self) -> Option<Self::Item> {
            if self.count < 5 {
                self.count += 1;
                Some(self.count)
            } else {
                None
            }
        }
    }

    let mut counter = Counter { count: 0 };
    assert_eq!(counter.next(), Some(1));
    assert_eq!(counter.next(), Some(2));
    assert_eq!(counter.next(), Some(3));
}

/// 测试关联类型在泛型中的使用
#[test]
fn test_associated_types_in_generics() {
    trait Container {
        type Item;
        fn get(&self) -> &Self::Item;
    }

    struct Box<T> {
        value: T,
    }

    impl<T> Container for Box<T> {
        type Item = T;
        fn get(&self) -> &T {
            &self.value
        }
    }

    fn get_item<C: Container>(container: &C) -> &C::Item {
        container.get()
    }

    let box_item = Box { value: 42 };
    assert_eq!(*get_item(&box_item), 42);
}

/// 测试关联类型与where子句
#[test]
fn test_associated_types_with_where() {
    trait Container {
        type Item;
        fn get(&self) -> &Self::Item;
    }

    fn process<C>(container: &C) -> &C::Item
    where
        C: Container,
        C::Item: Clone,
    {
        container.get()
    }

    struct Wrapper<T>(T);

    impl<T: Clone> Container for Wrapper<T> {
        type Item = T;
        fn get(&self) -> &T {
            &self.0
        }
    }

    let wrapper = Wrapper(42);
    assert_eq!(*process(&wrapper), 42);
}

/// 测试关联常量
#[test]
fn test_associated_constants() {
    trait Config {
        const MAX_SIZE: usize;
        const NAME: &'static str;
    }

    struct AppConfig;

    impl Config for AppConfig {
        const MAX_SIZE: usize = 100;
        const NAME: &'static str = "MyApp";
    }

    assert_eq!(AppConfig::MAX_SIZE, 100);
    assert_eq!(AppConfig::NAME, "MyApp");
}

/// 测试泛型关联类型 (GATs)
#[test]
fn test_generic_associated_types() {
    trait LendingIterator {
        type Item<'a>
        where
            Self: 'a;

        fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
    }

    struct Buffer<T> {
        data: Vec<T>,
        pos: usize,
    }

    impl<T> LendingIterator for Buffer<T> {
        type Item<'a>
            = &'a T
        where
            Self: 'a;

        fn next<'a>(&'a mut self) -> Option<&'a T> {
            if self.pos < self.data.len() {
                let item = &self.data[self.pos];
                self.pos += 1;
                Some(item)
            } else {
                None
            }
        }
    }

    let mut buffer = Buffer {
        data: vec![1, 2, 3],
        pos: 0,
    };

    assert_eq!(buffer.next(), Some(&1));
    assert_eq!(buffer.next(), Some(&2));
}

/// 测试关联类型作为类型别名
#[test]
fn test_associated_type_aliases() {
    trait Service {
        type Request;
        type Response;
        type Error;

        fn handle(&self, req: Self::Request) -> Result<Self::Response, Self::Error>;
    }

    struct HttpService;

    #[derive(Debug)]
    struct HttpRequest {
        #[allow(dead_code)]
        path: String,
    }

    #[derive(Debug)]
    struct HttpResponse {
        status: u16,
    }

    #[derive(Debug)]
    struct HttpError;

    impl Service for HttpService {
        type Request = HttpRequest;
        type Response = HttpResponse;
        type Error = HttpError;

        fn handle(&self, _req: Self::Request) -> Result<Self::Response, Self::Error> {
            Ok(HttpResponse { status: 200 })
        }
    }

    let service = HttpService;
    let req = HttpRequest {
        path: "/".to_string(),
    };
    let resp = service.handle(req).unwrap();
    assert_eq!(resp.status, 200);
}

/// 测试关联类型的默认实现
#[test]
fn test_default_associated_types() {
    trait Processor {
        type Input;
        type Output;

        fn process(&self, input: Self::Input) -> Self::Output;
    }

    struct UpperCaseProcessor;

    impl Processor for UpperCaseProcessor {
        type Input = String;
        type Output = String;

        fn process(&self, input: Self::Input) -> Self::Output {
            input.to_uppercase()
        }
    }

    let processor = UpperCaseProcessor;
    let result: String = processor.process("hello".to_string());
    assert_eq!(result, "HELLO");
}

/// 测试关联类型约束
#[test]
fn test_associated_type_constraints() {
    use std::fmt::Debug;

    trait Container {
        type Item: Debug + Clone;
        fn get(&self) -> &Self::Item;
    }

    struct Wrapper<T: Debug + Clone> {
        value: T,
    }

    impl<T: Debug + Clone> Container for Wrapper<T> {
        type Item = T;
        fn get(&self) -> &T {
            &self.value
        }
    }

    let wrapper = Wrapper {
        value: vec![1, 2, 3],
    };
    assert_eq!(wrapper.get().clone(), vec![1, 2, 3]);
}

/// 测试复杂关联类型模式
#[test]
fn test_complex_associated_type_pattern() {
    trait Database {
        type Connection;
        type Record;
        type Error;

        fn connect(&self) -> Result<Self::Connection, Self::Error>;
        fn query(&self, conn: &mut Self::Connection) -> Result<Vec<Self::Record>, Self::Error>;
    }

    #[derive(Debug)]
    struct MockDatabase;
    #[derive(Debug)]
    struct MockConnection;
    #[derive(Debug)]
    struct MockRecord {
        #[allow(dead_code)]
        id: u32,
    }
    #[derive(Debug)]
    struct MockError;

    impl Database for MockDatabase {
        type Connection = MockConnection;
        type Record = MockRecord;
        type Error = MockError;

        fn connect(&self) -> Result<Self::Connection, Self::Error> {
            Ok(MockConnection)
        }

        fn query(&self, _conn: &mut Self::Connection) -> Result<Vec<Self::Record>, Self::Error> {
            Ok(vec![MockRecord { id: 1 }, MockRecord { id: 2 }])
        }
    }

    let db = MockDatabase;
    let mut conn = db.connect().unwrap();
    let records = db.query(&mut conn).unwrap();
    assert_eq!(records.len(), 2);
}
