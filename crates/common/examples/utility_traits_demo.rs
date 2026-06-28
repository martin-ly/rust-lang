//! Common crate 工具 trait 示例
//!
//! 运行: cargo run -p common --example utility_traits_demo

use common::{Identifiable, Measurable, Validatable, Version};

#[derive(Debug, Clone, PartialEq)]
struct Package {
    id: u64,
    name: String,
    version: Version,
}

impl Identifiable for Package {
    type Id = u64;

    fn id(&self) -> &Self::Id {
        &self.id
    }
}

impl Validatable for Package {
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

impl Measurable for Package {
    fn size_bytes(&self) -> usize {
        std::mem::size_of::<Self>() + self.name.len()
    }
}

fn main() {
    let p1 = Package {
        id: 1,
        name: "common".to_string(),
        version: Version::new(1, 2, 3),
    };
    let _p2 = Package {
        id: 2,
        name: "common".to_string(),
        version: Version::new(1, 3, 0),
    };

    println!("p1 id: {}", p1.id());
    println!("p1 valid: {:?}", p1.validate());
    println!("p1 size: {} bytes", p1.size_bytes());
    println!("p1 version: {}", p1.version);
}
