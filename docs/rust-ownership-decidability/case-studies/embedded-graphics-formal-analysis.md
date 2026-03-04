# Embedded-Graphics显示库形式化分析

> **主题**: 嵌入式图形绘制
> **形式化框架**: 绘制原语 + 迭代器 + 零分配
> **参考**: embedded-graphics crate (<https://github.com/embedded-graphics/embedded-graphics>)

---

## 目录

- [Embedded-Graphics显示库形式化分析](#embedded-graphics显示库形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 绘制原语](#2-绘制原语)
    - [定义 PRIMITIVE-1 ( 基本图形 )](#定义-primitive-1--基本图形-)
    - [定义 PRIMITIVE-2 ( 像素迭代 )](#定义-primitive-2--像素迭代-)
  - [3. 迭代器模型](#3-迭代器模型)
    - [定义 ITER-1 ( 惰性求值 )](#定义-iter-1--惰性求值-)
    - [定理 ITER-T1 ( 零分配 )](#定理-iter-t1--零分配-)
  - [4. 显示目标](#4-显示目标)
    - [定义 TARGET-1 ( DrawTarget trait )](#定义-target-1--drawtarget-trait-)
    - [定义 TARGET-2 ( 帧缓冲 )](#定义-target-2--帧缓冲-)
  - [5. 变换与样式](#5-变换与样式)
    - [定义 STYLE-1 ( 样式属性 )](#定义-style-1--样式属性-)
    - [定义 TRANSFORM-1 ( 仿射变换 )](#定义-transform-1--仿射变换-)
  - [6. 定理与证明](#6-定理与证明)
    - [定理 CLIP-T1 ( 裁剪正确性 )](#定理-clip-t1--裁剪正确性-)
  - [7. 代码示例](#7-代码示例)
    - [示例1: 基本绘制](#示例1-基本绘制)
    - [示例2: 显示驱动实现](#示例2-显示驱动实现)
    - [示例3: 动画与双缓冲](#示例3-动画与双缓冲)
    - [示例4: 进度条组件](#示例4-进度条组件)

---

## 1. 引言

embedded-graphics特点：

- 纯Rust 2D图形库
- 零堆分配
- 迭代器式绘制
- 可移植显示驱动

---

## 2. 绘制原语

### 定义 PRIMITIVE-1 ( 基本图形 )

$$
\text{Primitive} = \text{Point} \mid \text{Line} \mid \text{Rectangle} \mid \text{Circle} \mid \text{Triangle} \mid \text{Text}
$$

### 定义 PRIMITIVE-2 ( 像素迭代 )

每个原语生成像素迭代器。

$$
\text{Iterator} : \text{Primitive} \to \{ (x, y, \text{color}) \}
$$

---

## 3. 迭代器模型

### 定义 ITER-1 ( 惰性求值 )

绘制操作不立即执行，而是返回迭代器。

$$
\text{draw}(p) : \text{Primitive} \to \text{impl Iterator<Item = Pixel>
$$

### 定理 ITER-T1 ( 零分配 )

绘制迭代器不分配堆内存。

$$
\forall p : \text{Primitive}.\ \text{draw}(p) \text{ uses } O(1) \text{ stack}
$$

---

## 4. 显示目标

### 定义 TARGET-1 ( DrawTarget trait )

```rust
trait DrawTarget {
    type Color;
    type Error;
    fn draw_iter(&mut self, pixels: impl Iterator<Item = Pixel<Self::Color>>) -> Result<(), Self::Error>;
}
```

### 定义 TARGET-2 ( 帧缓冲 )

$$
\text{Framebuffer} = [\text{Color}; W \times H]
$$

---

## 5. 变换与样式

### 定义 STYLE-1 ( 样式属性 )

$$
\text{Style} = (\text{stroke\_color}, \text{stroke\_width}, \text{fill\_color})
$$

### 定义 TRANSFORM-1 ( 仿射变换 )

$$
T(x, y) = (ax + by + tx, cx + dy + ty)
$$

---

## 6. 定理与证明

### 定理 CLIP-T1 ( 裁剪正确性 )

裁剪确保像素在显示边界内。

$$
\forall (x, y) \in \text{draw}(p).\ 0 \leq x < W \land 0 \leq y < H
$$

---

## 7. 代码示例

### 示例1: 基本绘制

```rust
use embedded_graphics::{
    pixelcolor::Rgb565,
    prelude::*,
    primitives::{Circle, Rectangle, Triangle},
    text::Text,
    mono_font::{MonoTextStyle, ascii::FONT_6X10},
};

fn draw_example<D: DrawTarget<Color = Rgb565>>(
    display: &mut D
) -> Result<(), D::Error> {
    // 填充矩形
    Rectangle::new(Point::new(10, 10), Size::new(100, 50))
        .into_styled(
            PrimitiveStyleBuilder::new()
                .fill_color(Rgb565::RED)
                .stroke_color(Rgb565::GREEN)
                .stroke_width(2)
                .build()
        )
        .draw(display)?;

    // 圆形
    Circle::new(Point::new(50, 100), 40)
        .into_styled(PrimitiveStyle::with_fill(Rgb565::BLUE))
        .draw(display)?;

    // 三角形
    Triangle::new(
        Point::new(150, 100),
        Point::new(200, 150),
        Point::new(100, 150),
    )
    .into_styled(PrimitiveStyle::with_stroke(Rgb565::YELLOW, 3))
    .draw(display)?;

    // 文本
    Text::new("Hello Rust!", Point::new(10, 200), MonoTextStyle::new(
        &FONT_6X10,
        Rgb565::WHITE,
    ))
    .draw(display)?;

    Ok(())
}
```

### 示例2: 显示驱动实现

```rust
use embedded_graphics::draw_target::DrawTarget;
use embedded_graphics::pixelcolor::Rgb565;
use embedded_hal::digital::OutputPin;

struct ST7735<SPI, DC, RST> {
    spi: SPI,
    dc: DC,
    rst: RST,
    width: u16,
    height: u16,
}

impl<SPI, DC, RST> DrawTarget for ST7735<SPI, DC, RST>
where
    SPI: embedded_hal::spi::SpiDevice,
    DC: OutputPin,
    RST: OutputPin,
{
    type Color = Rgb565;
    type Error = DisplayError;

    fn draw_iter<I>(&mut self, pixels: I) -> Result<(), Self::Error>
    where
        I: IntoIterator<Item = Pixel<Self::Color>>,
    {
        for Pixel(coord, color) in pixels {
            self.set_pixel(coord.x as u16, coord.y as u16, color)?;
        }
        Ok(())
    }

    fn clear(&mut self, color: Self::Color) -> Result<(), Self::Error> {
        self.fill_rect(0, 0, self.width, self.height, color)
    }
}

impl<SPI, DC, RST> ST7735<SPI, DC, RST> {
    fn set_pixel(&mut self, x: u16, y: u16, color: Rgb565) -> Result<(), DisplayError> {
        self.set_address_window(x, y, x, y)?;
        self.write_pixel(color)
    }
}
```

### 示例3: 动画与双缓冲

```rust
use embedded_graphics::image::Image;
use tinybmp::Bmp;

fn animation_example() {
    // 加载BMP图像（编译时嵌入）
    let bmp: Bmp<Rgb565> = Bmp::from_slice(include_bytes!("image.bmp")).unwrap();
    let image = Image::new(&bmp, Point::new(10, 10));

    // 在帧缓冲之间切换
    let mut fb1 = [Rgb565::BLACK; 320 * 240];
    let mut fb2 = [Rgb565::BLACK; 320 * 240];

    let mut front = &mut fb1[..];
    let mut back = &mut fb2[..];

    loop {
        // 绘制到后备缓冲
        back.fill(Rgb565::BLACK);
        image.draw(&mut FramebufferTarget(back)).unwrap();

        // 交换
        core::mem::swap(&mut front, &mut back);

        // 显示前台缓冲
        display.show(front);
    }
}
```

### 示例4: 进度条组件

```rust
struct ProgressBar {
    position: Point,
    size: Size,
    progress: u8,  // 0-100
}

impl ProgressBar {
    fn draw<D: DrawTarget<Color = Rgb565>>(&self, target: &mut D) -> Result<(), D::Error> {
        // 背景
        Rectangle::new(self.position, self.size)
            .into_styled(PrimitiveStyle::with_fill(Rgb565::BLACK))
            .draw(target)?;

        // 进度填充
        let fill_width = (self.size.width as u32 * self.progress as u32 / 100) as u32;
        Rectangle::new(
            self.position,
            Size::new(fill_width as u32, self.size.height)
        )
        .into_styled(PrimitiveStyle::with_fill(Rgb565::GREEN))
        .draw(target)?;

        // 边框
        Rectangle::new(self.position, self.size)
            .into_styled(PrimitiveStyle::with_stroke(Rgb565::WHITE, 1))
            .draw(target)?;

        Ok(())
    }
}
```

---

**维护者**: Rust Embedded Formal Methods Team
**创建日期**: 2026-03-05
**状态**: ✅ 已对齐
