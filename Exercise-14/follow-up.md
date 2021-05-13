# Exercise 14: Token-based deduplication

In that case the incoming message will be retried, the tokens will be generated again and the outgoing messages will be dispatched referencing the new tokens. Result? Business logic executed multiple times. How can we prevent this?

We need to add a `bool TokensGenerated {get; set;}` property to the `OutboxState` to prevent re-generating tokens. Now go back to the `OutboxBehavior`. We need to ensure that only the last generated values for tokens are persisted in the messages.

Mark the tokens as created and add a store call after the `foreach` loop

```c#
outboxState.TokensGenerated = true;
version = await repository.Put(entity, version);
```

Finally, put the entire token generation code and the store call above in an `if` clause guarded by `!outboxState.TokensGenerated`:

```c#
if (!outboxState.TokensGenerated)
{
    foreach (var outgoingMessage in outboxState.OutgoingMessages)
    {
        var token = Guid.NewGuid().ToString();
        outgoingMessage.Headers["TokenId"] = token;
        await tokenStore.Create(token);
    }

    outboxState.TokensGenerated = true;
    version = await repository.Put(entity, version);
}
```

Now let's run our code.