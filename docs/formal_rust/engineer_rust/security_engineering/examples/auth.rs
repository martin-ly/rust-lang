// 安全工程：认证接口示例 Security Engineering: Auth Interface Example
trait Auth {
    fn authenticate(&self, user: &str, pass: &str) -> bool;
}

struct SimpleAuth;

impl Auth for SimpleAuth {
    fn authenticate(&self, user: &str, pass: &str) -> bool {
        user == "admin" && pass == "password"
    }
}

fn main() {
    let auth = SimpleAuth;
    println!("Login: {}", auth.authenticate("admin", "password"));
} 