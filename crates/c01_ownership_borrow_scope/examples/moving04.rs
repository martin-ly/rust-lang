struct Builder {
    value: String,
}

impl Builder {
    // 创建一个新的 Builder 实例
    fn new() -> Self {
        Builder {
            value: String::new(),
        }
    }

    // 添加字符串并返回自身以支持链式调用
    fn append(mut self, text: &str) -> Self {
        self.value.push_str(text);
        self // 移动 self
    }

    // 添加换行符并返回自身以支持链式调用
    fn newline(mut self) -> Self {
        self.value.push('\n');
        self // 移动 self
    }

    // 打印最终结果
    fn build(self) -> String {
        self.value // 移动 value
    }
}

fn main() {
    let result = Builder::new()
        .append("Hello,")
        .newline()
        .append("World!")
        .build();

    println!("{}", result);
}

// 该代码说明：
//函数 Builder::new：创建一个新的 Builder 实例。
//函数 Builder::append：添加字符串并返回自身以支持链式调用。
//函数 Builder::newline：添加换行符并返回自身以支持链式调用。
//函数 Builder::build：打印最终结果。
