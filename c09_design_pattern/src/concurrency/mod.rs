pub mod asynchronous;
pub mod message_passing;
pub mod producer_consumer;
pub mod reader_writer;
pub mod shared_state;
pub mod task_scheduling;

/*
并发:
    关注如何在同一时间段内处理多个任务，通常通过多线程或多进程实现。

异步:
    关注如何在不阻塞的情况下处理任务，通常在单线程中通过事件循环实现。

从并发的角度看，异步是并发的一种实现方式。
两者可以结合使用，以提高程序的性能和响应性.
*/
