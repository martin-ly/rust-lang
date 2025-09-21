fn main() {
    println!("c12_middlewares example");
    println!("features:");
    println!("  kv-redis: {}", cfg!(feature = "kv-redis"));
    println!("  sql-postgres: {}", cfg!(feature = "sql-postgres"));
    println!("  sql-mysql: {}", cfg!(feature = "sql-mysql"));
    println!("  sql-sqlite: {}", cfg!(feature = "sql-sqlite"));
    println!("  mq-nats: {}", cfg!(feature = "mq-nats"));
    println!("  mq-kafka: {}", cfg!(feature = "mq-kafka"));
    println!("  mq-mqtt: {}", cfg!(feature = "mq-mqtt"));
    println!("  proxy-nix: {}", cfg!(feature = "proxy-nix"));
}
