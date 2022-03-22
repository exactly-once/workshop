# Exercise 17: Generic outbox - part 3

The solution looks really good but we can make it even better. Message serialization is a very important aspect of every distributed system. Sometimes this serialization is quite complex.

In the current solution, messages are serialized in two ways. First, they are serialized as part of the `Order` aggregate using whatever mechanism the data store uses. Then, they are serialized for sending over the wire. This may cause problems, especially with more complex data types.

In this exercise we're going to dive deeper into the messaging framework and plug in a mechanism that allows storage of wire-formatted messages in the outbox.

- In the `OutboxState`, replace the `Message` class with the built in `NServiceBus.Transport.TransportOperation` class and make it an array instead of a list.
- Replace the call to `next()` on line 38 of the `OutboxBehavior` with a call to `InvokeMessageHandler`. Assign the returned value to `order.OutgoingMessages[context.MessageId].OutgoingMessages`
- Replace the `forach` loop with a call to `await Dispatch`.
- Replace the calls to `outboxState.OutgoingMessages.Add` in the `AddItemHandler` to `context.Publish`. Remember to `await` this call.
- You can remove the `outboxState` from the `AddItemHandler` now. 

- That's quite an achievement! There is no more deduplication logic in the message handler!
