# Exercise 11: Deterministic message generation

In the last exercise we are going to bring back the order, once and for all. The only practical way of ensuring messages are generated in a deterministic way is to store them as part of our business transactions.

Let's pause here for a moment and think about the following statement.

> Message handles should be idempotent

What we usually think about is how to modify the data in such a way that when we run the code multiple times, the data continues to be in the same state as after the first modification.

We don't don't think about what happens if, between re-running our logic the data is modified by someone else. We also don't think about the messages we are sending out.

Let's repeat what we said: the only practical way of ensuring messages are generated in a deterministic way is to store them as part of our business transactions. We are going to do just that.

OK, now let's get our hands dirty with code. 

- Navigate the `Order` class and add a new property `OutgoingMessages` of type `Dictionary<string, object>`. This property is going to store our generated messages.
- Navigate to the `AddItemHandler` class. You should feel familiar here by now.
- Invert the `if` statement in the beginning of the method and remove `else` branch (the one that does the logging).
- Move the `PublishWithId` statements up to the business logic part, between `order.ProcessedMessages.Add` and `orderRepository.Store`.
- Replace the deterministic ID generation with `Guid.NewGuid()`. 
- Replace the `context.PublishWithId` calls with `order.OutgoingMessages.Add(messageId, messageObject)`.

After these changes your business logic should be correctly _storing_ the outgoing messages. But it does not yet send them out. For that we need to add the _dispatching_ code below. Here's how it should look:

```c#
if (order.OutgoingMessages.Any())
{
    foreach (var kvp in order.OutgoingMessages)
    {
        await context.PublishWithId(kvp.Value, kvp.Key);
    }
    order.OutgoingMessages.Clear();
    await orderRepository.Store(order);
}
```

As you can see, we are pushing all the messages from the `OutgoingMessages` collection, erasing them and updating our order.

Now run the solution and try submitting and order with two items of *pierogi* with strawberries. Remember, last time this caused the `FirstItemAdded` event to be omitted due to a simulated timeout.

What happens this time? Can you explain why the `FirstItemAdded` reaches the marketing service _before_ the timeout happens?