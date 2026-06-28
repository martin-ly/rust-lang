//! Common crate 集成测试

use common::{Comparable, Identifiable, Measurable, RustLangError, Validatable, Version};

#[derive(Debug, Clone, PartialEq)]
struct Item {
    id: u64,
    name: String,
    version: Version,
}

impl Identifiable for Item {
    type Id = u64;

    fn id(&self) -> &Self::Id {
        &self.id
    }
}

impl Validatable for Item {
    type Error = String;

    fn validate(&self) -> Result<(), Self::Error> {
        if self.name.is_empty() {
            Err("name cannot be empty".to_string())
        } else if self.version.major() == 0 {
            Err("major version must be > 0".to_string())
        } else {
            Ok(())
        }
    }
}

impl Measurable for Item {
    fn size_bytes(&self) -> usize {
        std::mem::size_of::<Self>() + self.name.len()
    }
}

#[test]
fn test_identifiable() {
    let item = Item {
        id: 42,
        name: "test".to_string(),
        version: Version::new(1, 0, 0),
    };
    assert_eq!(*item.id(), 42);
}

#[test]
fn test_validatable() {
    let valid = Item {
        id: 1,
        name: "ok".to_string(),
        version: Version::new(1, 0, 0),
    };
    let invalid_name = Item {
        id: 2,
        name: "".to_string(),
        version: Version::new(1, 0, 0),
    };
    let invalid_version = Item {
        id: 3,
        name: "ok".to_string(),
        version: Version::new(0, 1, 0),
    };
    assert!(valid.validate().is_ok());
    assert!(invalid_name.validate().is_err());
    assert!(invalid_version.validate().is_err());
}

#[test]
fn test_comparable() {
    let x = 5;
    assert!(x.in_range(&1, &10));
    assert!(!x.in_range(&10, &20));
}

#[test]
fn test_measurable() {
    let item = Item {
        id: 1,
        name: "hello".to_string(),
        version: Version::new(1, 0, 0),
    };
    assert!(item.size_bytes() > 0);
    assert!(!item.is_empty());
}

#[test]
fn test_version_display() {
    let v = Version::new(1, 2, 3);
    assert_eq!(format!("{}", v), "1.2.3");
}

#[test]
fn test_common_error_basic() {
    use common::CommonError;
    let err = CommonError::NotFound("resource".to_string());
    assert_eq!(err.error_code(), common::ErrorCode::NotFound);
    assert!(!err.is_retryable());
}
