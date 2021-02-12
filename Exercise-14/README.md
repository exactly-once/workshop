# Exercise 14: Token-based deduplication

We have just discussed the idea of sync-async boundary. As a reminder, this boundary delimits the part of the system which is highly interactive and the part that is not. On one side the synchronous communication allows users to efficiently work with the system. On the other side asynchronous communication allows build complex business processed with simple and loosely coupled message-driven components.

We have also discussed how our past approaches to deduplication are non-deterministic in nature. In our next exercise we are going to explore an alternative approach -- one that is deterministic.

This approach is based on inverting the *is duplicate* check. Instead of a positive check

> a message is a duplicate is there exist evidence for processing it

we are going to use a negative check

> a message is a duplicate is if a token required for processing it does not exist

This approach guarantees that the deduplication data has bounded size (proportional to the number of in-flight messages) and that deduplication checks are not dependent on the wall clock.

First, let's create a token store. Instead of creating one from scratch, we will reuse the `InboxStore` class.
 - Rename `IInboxStore` to `ITokenStore` and `InboxStore` to `TokenStore`
 - Rename `InboxItem` to `Token`
 - Rename `HasBeenProcessed` to `Exists` and the parameter name to `tokenId`
 - Rename `MarkProcessed` to `Create` and the parameter name `tokenId`

We are also going to need a `Delete` method. It is already defined on the `Repository` class so we only need to add it to `ITokenStore`. To make it more convenient let's use `Task Delete(string tokenId, string version)` signature. Now you probably ask where are we going to get the version from. The `Repository` returns the version value from `Get` but our `Exists` method does not return it. Let's fix that and make `Exists` return a tuple `(bool, string)`.

Now go to the `OutboxBehavior` and invert the check that now calls the token store. Store the token version in a variable. We will need it. You may ask if it is OK that we pass the message ID as a parameter we called `tokenId`. And it actually is not OK but we will deal with that later. Now turn your attention to the bottom part of the method where we used to populate the inbox. After our renames it contains the `tokenStore.Create` call. We need to invert this one also. It becomes `tokenStore.Delete` and we need to pass our token version here.

Are we done? From the perspective of this endpoint, yes. But what about dispatching messages to the downstream endpoints? There is no code that creates tokens for them so they would not be processed. Let's fix that.

Add a `foreach` clause that iterates over `outboxState.OutgoingMessages` before the dispatch code and add a `TokenId` header containing a Guid value. Don't forget to also created this token via `tokenStore.Create`. Now go back to the `Exist` check and replace the message ID parameter with the value of the `TokenId` header on the incoming message: `context.Headers.TryGetValue("TokenId", out var tokenId)`. Do the same in the `tokenStore.Delete` call. 

What if there is no token ID on a message? The `SendSubmitOrder` message won't contain the token because it is sent from outside of a handler. In this case we don't want to treat the message as a duplicate and we don't want to delete the token (that does not exist). Let's add guard statements `tokenId != null`.

Are we done? Almost. Consider what happens if the code fails right after dispatching the messages.