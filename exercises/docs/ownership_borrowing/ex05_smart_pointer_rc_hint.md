# 提示: Rc 智能指针共享所有权

Rc::clone 不会深拷贝数据，只是增加引用计数。使用 Rc::strong_count 查看计数。

## 相关阅读

- 项目内对应模块: `crates/` 下的相关源码
- 速查卡: `docs/02_reference/quick_reference/`
