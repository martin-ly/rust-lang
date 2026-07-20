use std::any::Any;
use std::collections::HashMap;
use std::fmt::Debug;

// 定义消息特征
#[allow(unused)]
trait Message: Debug + 'static {
    fn as_any(&self) -> &dyn Any;
}

// 定义中介者特征
#[allow(unused)]
trait Mediator {
    fn send(&mut self, msg: &dyn Message, sender_id: usize);
    fn register<C: Colleague>(&mut self, colleague: C) -> usize;
}

// 定义同事特征
#[allow(unused)]
trait Colleague: Debug + 'static {
    fn receive(&mut self, msg: &dyn Message, sender_id: usize);
    fn get_id(&self) -> usize;
    fn set_id(&mut self, id: usize);
    fn as_any_mut(&mut self) -> &mut dyn Any;
}

// 具体中介者：聊天室
#[allow(unused)]
#[derive(Debug, Default)]
struct ChatRoom {
    colleagues: HashMap<usize, Box<dyn Colleague>>,
    next_id: usize,
}

impl ChatRoom {
    fn new() -> Self {
        ChatRoom {
            colleagues: HashMap::new(),
            next_id: 0,
        }
    }
}

impl Mediator for ChatRoom {
    fn send(&mut self, msg: &dyn Message, sender_id: usize) {
        println!("中介者接收到消息: {:?} 来自 ID: {}", msg, sender_id);

        // 将消息转发给除发送者外的所有同事
        for (id, colleague) in &mut self.colleagues {
            if *id != sender_id {
                colleague.receive(msg, sender_id);
            }
        }
    }

    fn register<C: Colleague>(&mut self, mut colleague: C) -> usize {
        let id = self.next_id;
        self.next_id += 1;

        colleague.set_id(id);
        self.colleagues.insert(id, Box::new(colleague));
        id
    }
}

// 文本消息实现
#[derive(Debug, Clone)]
struct TextMessage {
    content: String,
}

impl Message for TextMessage {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

// 图片消息实现
#[derive(Debug, Clone)]
struct ImageMessage {
    url: String,
    size: (u32, u32),
}

impl Message for ImageMessage {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

// 用户实现
#[derive(Debug)]
struct User {
    name: String,
    id: usize,
}

#[allow(unused)]
impl User {
    fn new(name: String) -> Self {
        User { name, id: 0 }
    }

    fn send_text<M: Mediator>(&self, mediator: &mut M, content: String) {
        let msg = TextMessage { content };
        mediator.send(&msg, self.id);
    }

    fn send_image<M: Mediator>(&self, mediator: &mut M, url: String, size: (u32, u32)) {
        let msg = ImageMessage { url, size };
        mediator.send(&msg, self.id);
    }
}

impl Colleague for User {
    fn receive(&mut self, msg: &dyn Message, sender_id: usize) {
        if let Some(text_msg) = msg.as_any().downcast_ref::<TextMessage>() {
            println!(
                "用户 {} 收到来自用户 {} 的文本消息: {}",
                self.name, sender_id, text_msg.content
            );
        } else if let Some(img_msg) = msg.as_any().downcast_ref::<ImageMessage>() {
            println!(
                "用户 {} 收到来自用户 {} 的图片消息: {} 尺寸: {:?}",
                self.name, sender_id, img_msg.url, img_msg.size
            );
        }
    }

    fn get_id(&self) -> usize {
        self.id
    }

    fn set_id(&mut self, id: usize) {
        self.id = id;
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

// 机器人用户实现
#[derive(Debug)]
struct Bot {
    name: String,
    id: usize,
    keywords: Vec<String>,
}

impl Bot {
    fn new(name: String, keywords: Vec<String>) -> Self {
        Bot {
            name,
            id: 0,
            keywords,
        }
    }
}

impl Colleague for Bot {
    fn receive(&mut self, msg: &dyn Message, sender_id: usize) {
        if let Some(text_msg) = msg.as_any().downcast_ref::<TextMessage>() {
            for keyword in &self.keywords {
                if text_msg.content.contains(keyword) {
                    println!(
                        "机器人 {} 检测到关键词 '{}' 在用户 {} 的消息中",
                        self.name, keyword, sender_id
                    );
                    return;
                }
            }
            println!(
                "机器人 {} 收到来自用户 {} 的消息，但没有匹配任何关键词",
                self.name, sender_id
            );
        }
    }

    fn get_id(&self) -> usize {
        self.id
    }

    fn set_id(&mut self, id: usize) {
        self.id = id;
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

#[allow(unused)]
fn mediator_test() {
    // 创建中介者
    let mut chat_room = ChatRoom::new();

    // 创建同事
    let alice = User::new(String::from("Alice"));
    let bob = User::new(String::from("Bob"));
    let bot = Bot::new(
        String::from("InfoBot"),
        vec![String::from("info"), String::from("help")],
    );

    // 注册同事
    let alice_id = chat_room.register(alice);
    let bob_id = chat_room.register(bob);
    let _bot_id = chat_room.register(bot);

    // 准备消息
    let text_msg1 = TextMessage {
        content: String::from("你好，Bob！"),
    };
    let text_msg2 = TextMessage {
        content: String::from("我需要一些信息，能帮助我吗？"),
    };
    let img_msg = ImageMessage {
        url: String::from("http://example.com/image.jpg"),
        size: (800, 600),
    };

    // 手动发送消息
    chat_room.send(&text_msg1, alice_id);
    chat_room.send(&text_msg2, bob_id);
    chat_room.send(&img_msg, alice_id);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mediator01() {
        mediator_test();
    }
}
