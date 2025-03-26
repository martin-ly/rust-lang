use std::sync::{Arc, Mutex};

// 命令 trait
trait Command {
    fn execute(&self);
}

// 具体命令
struct LightOnCommand {
    light: Arc<Mutex<Light>>,
}

impl LightOnCommand {
    fn new(light: Arc<Mutex<Light>>) -> Self {
        LightOnCommand { light }
    }
}

impl Command for LightOnCommand {
    fn execute(&self) {
        let mut light = self.light.lock().unwrap();
        light.turn_on();
    }
}

#[allow(unused)]
struct LightOffCommand {
    light: Arc<Mutex<Light>>,
}

impl LightOffCommand {
    fn new(light: Arc<Mutex<Light>>) -> Self {
        LightOffCommand { light }
    }
}

impl Command for LightOffCommand {
    fn execute(&self) {
        let mut light = self.light.lock().unwrap();
        light.turn_off();
    }
}

// 接收者
#[allow(unused)]
struct Light {
    is_on: bool,
}

impl Light {
    fn new() -> Self {
        Light { is_on: false }
    }

    fn turn_on(&mut self) {
        self.is_on = true;
        println!("灯已打开");
    }

    fn turn_off(&mut self) {
        self.is_on = false;
        println!("灯已关闭");
    }
}

// 调用者
#[allow(unused)]
struct RemoteControl {
    command: Option<Arc<dyn Command>>,
}

#[allow(unused)]
impl RemoteControl {
    fn set_command(&mut self, command: Arc<dyn Command>) {
        self.command = Some(command);
    }

    fn press_button(&self) {
        if let Some(command) = &self.command {
            command.execute();
        } else {
            println!("没有命令设置");
        }
    }
}

/*
代码说明：
    命令 Trait：
        定义了一个 Command trait，包含 execute 方法。
    具体命令：
        LightOnCommand 和 LightOffCommand 是具体的命令实现，分别用于打开和关闭灯。
    接收者：
        Light 结构体表示接收者，包含打开和关闭灯的逻辑。
    调用者：
        RemoteControl 结构体用于设置命令并执行命令。
    主函数：
        在主函数中创建灯和命令对象，并通过遥控器执行命令。
*/

#[allow(unused)]
fn command() {
    let light = Arc::new(Mutex::new(Light::new()));

    let light_on = Arc::new(LightOnCommand::new(light.clone()));
    let light_off = Arc::new(LightOffCommand::new(light.clone()));

    let mut remote = RemoteControl { command: None };
    remote.press_button();
    // 打开灯
    remote.set_command(light_on);
    remote.press_button();

    // 关闭灯
    remote.set_command(light_off);
    remote.press_button();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_command01() {
        command();
    }
}

