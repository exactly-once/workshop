# Exercise 2: Message duplication on the receiver side

The NServiceBus Azure Storage Queues transport uses the [Peek-Lock](https://docs.microsoft.com/en-us/rest/api/servicebus/peek-lock-message-non-destructive-read) API to receive messages without destroying them. The lock hides the message on the queue from competing consumers and is held for 30 seconds, after which the message becomes visible to other consumers. Since the `Orders` endpoint is multi-threaded, it immediately fetches the message again, in another thread.

As a result, the message is never going to be consumed. This showcases an extreme scenario. In a real world system, everything would be fine in the testing environment (where the load is small). It would even work in production for a couple of weeks until a higher load is experienced and the database starts to lag. A couple of messages are processed slower than usual and later picked up again, adding even more load to an already struggling system.
