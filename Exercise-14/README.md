# Exercise 14: Token-based deduplication

We have just discussed the idea of sync-async boundary. As a reminder, this boundary delimits the part of the system which is highly interactive and the part that is not. On one side the synchronous communication allows users to efficiently work with the system. On the other side asynchronous communication allows build complex business processed with simple and loosely coupled message-driven components.

We have also discussed how our past approaches to deduplication are non-deterministic in nature. In our next exercise we are going to explore an alternative approach -- one that is deterministic.

This approach is based on inverting the *is duplicate* check. Instead of a positive check

> a message is a duplicate is there exist evidence for processing it

we are going to use a negative check

> a message is a duplicate is if a token required for processing it does not exist

This approach guarantees that the deduplication data has bounded size (proportional to the number of in-flight messages) and that deduplication checks are not dependent on the wall clock.

To see how the inverted marking logic is supposed to work, navigate to the `IInboxStore` file. In now contains also an interface for the token store. To make the comparison easier we included the HTTP verbs that match the operations. Notice how the GET now returns the inverted value and how `MarkProcessed` has been changed from `PUT` to `DELETE`. We now also have an additional method - `Create` to create the tokens.

Now go to the `OutboxBehavior`. Notice we already changed the code to use the token store but it does not compile yet. Fix it by using the `HasNotBeenProcessed` method. Remember to the negation. Store the token version in a variable. We will need it.

```c#
var (hasNotBeenProcessed, tokenVersion) = await tokenStore.HasNotBeenProcessed(context.MessageId);
```

You may ask if it is OK that we pass the message ID as a parameter we called `tokenId`. And it actually is not OK but we will deal with that later. 

Now turn your attention to the bottom part of the method where we used to populate the inbox. Notice that we now call `tokenStore.MarkProcessed` there. The intent is the same but remember that the underlying storage action is now `DELETE` rather than `PUT`. What is missing is the `tokenVersion` perameter. When we delete we need to ensure we are still *owners* of the token.

Are we done? From the perspective of this endpoint, yes. But what about dispatching messages to the downstream endpoints? There is no code that creates tokens for them so they would not be processed. Let's fix that.

Add a `foreach` clause that iterates over `outboxState.OutgoingMessages` before the dispatch code and add a `TokenId` header containing a Guid value. Don't forget to also create this token via `tokenStore.Create`. 

```c#
var token = Guid.NewGuid().ToString();
outgoingMessage.Headers["TokenId"] = token;
await tokenStore.Create(token);
```

Now go back to the `tokenStore.HasNotBeenProcessed` check and replace the message ID parameter with the value of the `TokenId` header on the incoming message: `context.Headers.TryGetValue("TokenId", out var tokenId)`. Do the same in the `tokenStore.MarkProcessed` call. 

Are we done? Almost. Consider what happens if the code fails right after dispatching the messages.