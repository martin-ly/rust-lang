/*
在Rust中，struct（结构体）是一种自定义数据类型，用于将多个相关的值组合在一起。
结构体可以包含不同类型的数据，并且可以通过字段名来访问这些数据。

结构体的定义和解释
定义：
    结构体使用struct关键字定义，后面跟着结构体的名称和字段的定义。
    每个字段都有一个名称和类型。
解释：
    结构体用于表示一个具有多个属性的对象，适合用于组织和管理相关的数据。
    结构体可以是简单的，也可以是嵌套的，甚至可以包含其他结构体。

*/

#[derive(Debug)]
struct Person {
    name: String,
    age: u32,
}

#[allow(unused)]
pub fn define_struct() {
    let person = Person {
        name: String::from("Alice"),
        age: 30,
    };
    println!("Name: {}, Age: {}", person.name, person.age);
    println!("{:?}", person);
}

struct Author {
    name: String,
    age: u32,
}

struct Book {
    title: String,
    author: Author,
    pages: u32,
}

#[allow(unused)]
pub fn define_struct_2() {
    let author = Author {
        name: String::from("George Orwell"),
        age: 46,
    };

    let book = Book {
        title: String::from("1984"),
        author, // 使用结构体
        pages: 328,
    };

    println!("Book Title: {}", book.title);
    println!("Author: {}, Age: {}", book.author.name, book.author.age);
    println!("Pages: {}", book.pages);
}
