# Exercise 2: Message duplication on the receiver side

The NServiceBus Azure Storage Queues transport uses [Peek-Lock](https://docs.microsoft.com/en-us/rest/api/servicebus/peek-lock-message-non-destructive-read) API to receive messages without destroying them. The lock is held for 30 seconds after which the message becomes visible again. Because the `Orders` endpoint is multi-threaded, it immediately fetches the message again, in another thread.

As a result, the message is never ever going to be consumed. This is of course an extreme case. In real world system everything would be fine in the testing environment (where the load is small). It would even work in production for a couple of weeks until a higher load is experienced and the database starts to lag behind. A couple of messages are processed slower than usual and they are picked up again, adding even more load to an already struggling system.
