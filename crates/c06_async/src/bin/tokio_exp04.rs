use crossterm::{
    event::{self, KeyCode, EnableMouseCapture, DisableMouseCapture},
    execute,
    terminal::{self, ClearType},
};
use std::io::{self};
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() -> io::Result<()> {
    // 启用终端的鼠标捕获
    let mut stdout = io::stdout();
    execute!(stdout, EnableMouseCapture)?;
    terminal::enable_raw_mode()?;
    execute!(stdout, terminal::Clear(ClearType::All))?;

    println!("按 'q' 退出程序。");

    let mut count = 0;

    loop {
        // 检查是否有键盘事件
        if event::poll(Duration::from_millis(300))? {
            if let event::Event::Key(key_event) = event::read()? {
                if key_event.code == KeyCode::Char('q') {
                    break; // 按下 'q' 键退出
                }
            }
        }

        // 每秒增加计数
        count += 1;
        println!("计数: {}", count);
        sleep(Duration::from_secs(1)).await; // 异步等待
    }

    // 清理终端
    terminal::disable_raw_mode()?;
    execute!(stdout, DisableMouseCapture)?;
    println!("程序已退出。");

    Ok(())
}
