# Exercise 14: Token-based deduplication

In that case the incoming message will be retried, the tokens will be generated again and the outgoing messages will be dispatched referencing the new tokens. Result? Business logic executed multiple times. How can we prevent this?

We need to add a `bool TokensGenerated {get; set;}` property to the `OutboxState` to prevent re-generating tokens. After doing it add an `if` clause based on it around the token generation. Last but not least, we need to set that property to true and flush the changes to the database *before* dispatching messages. Can you tell why?

Now let's run our code.