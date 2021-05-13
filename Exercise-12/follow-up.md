# Exercise 12: Generic outbox - follow-up

The solution looks really good but we can make it even better. So far we stored our business messages in the outbox. The downside of that is that headers, which are an essential parts of a message, were missing. We'll fix that now.

Let's start by combining `ProcessedMessages` and `OutgoingMessages` collections into a single one. The goal is to implement the following logic:

**If the `OutgoingMessages` dictionary contains a non-null value for a message ID, that message has been processed but the resulting outgoing messages have not been dispatched. If it contains `null` then that message have been processed and resulting outgoing messages dispatched. If it does not contain that value, the message has not been processed.**

- Change the type for the `OutgoingMessages` property of the `Order` to `Dictionary<string, OutboxState>`. The `OutboxState` type represents a collection of complete serialized messages (including the headers). This is a significant change since from now on the key is going to be the ID of the **incoming message** while the ID of the outgoing message is going to be part of the value
- Change the _has been processed_ condition `!order.ProcessedMessages.Contains(context.MessageId)` to use the `OutgoingMessages` property: `!order.OutgoingMessages.ContainsKey(context.MessageId)`
- Change the _mark as processed_ statement (`order.ProcessedMessages.Add(context.MessageId);`) in the `AddItemHandler` to use the `OutgoingMessages` property: `var outboxState = new OutboxState(); order.OutgoingMessages.Add(context.MessageId, outboxState)`
- Notice that this statement can be moved to the `OutboxBehavior` just prior to the call to `next()`. Do that. Then put the `outboxState` into the context by doing `context.Extensions.Set(outboxState)`
- Retrieve the `outboxState` in the `AddItemHandler` via `context.Extensions.Get<OutboxState>();`
- Replace the calls to `order.OutgoingMessages.Add` for publishing messages with `outboxState.OutgoingMessages.Add(new Message(...`
- Change the condition for dispatching outgoing messages to take into account the new structure of `OutgoingMessages`. Change `if (order.OutgoingMessages.Any())` to `order.OutgoingMessages[context.MessageId] != null`. Notice that we don't need to check if the value for the key exists because the structure code guarantees that.
- Replace the `order.OutgoingMessages` with `order.OutgoingMessages[context.MessageId].OutgoingMessages` in the `foreach`
- Replace the reference to `Value` with `Payload` and `Key` with `Id`.
- Replace the `order.OutgoingMessages.Clear()` with `order.OutgoingMessages[context.MessageId] = null` to prevent removing the information about all processed messages
- You can now safely remove the `ProcessedMessages` property and all its references. You can comment out the `RemoveItemHandler`. You can deal with that one later as an extra exercise.

Run the solution to check if it works. Now it is time for the last final step -- store serialized messages with headers in the outbox. In order to do that we will take advantage of an extensibility point within NServiceBus that allows us to intercept outgoing messages from a behavior in the pipeline. We will use the `Dispatch` and `InvokeMessageHandler` helper methods.

- In the `OutboxState` replace the `Message` class with built in `NServiceBus.Transport.TransportOperation` and make it an array instead of a list.
- Replace the call to `next()` with a call to `InvokeMessageHandler`. Assign the returned value to `order.OutgoingMessages[context.MessageId].OutgoingMessages`
- Replace the `forach` loop with a call to `Dispatch`.
- Replace the calls to `outboxState.OutgoingMessages.Add` in the `AddItemHandler` to `context.Publish`. Drop the ID. The framework will generate one for you. Remember to `await` this call.
- You can remove the `outboxState` from the `AddItemHandler` now. That's quite an achievement! There is no more deduplication logic in the message handler!
