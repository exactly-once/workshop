# Exercise 12: Generic outbox

In the previous exercise we implemented the Outbox pattern inline in the handler of the `AddItem` message. While it did solve our problem, it is not ideal from the code reuse perspective. Who would like to have the same code copied over and over again? In this exercise we are going to extract that piece of code and make it more generic. In order to achieve this we will use the *behavior* extension system of NServiceBus; the same one that we previously used to simulate various failure conditions.

Now let's get our hands dirty. First move the repository to the behavior

- In the `OutboxBehavior`, before passing the invocation further in line 27, load the order from the repository and add it to the context.
  - Load the order based on the `OrderId` property of the `orderMessage`
  - Put it in the handling context: `context.Extensions.Set(order);`
- Persist the changes done to the order via `orderRepository.Store` after the call to `next()` (this line invokes the message handlers)
- Replace usages of repository in the `AddItemHandler` with usages of the `Order` instance managed by the `OutboxBehavior`
  - Replace the repository usage with retrieving the `Order` from the context: `var order = context.Extensions.Get<Order>();`
  - Remove the second call to `orderRepository.Store` as it is handled by the behavior
- Run the code

- Move the code responsible for pushing out generated messages to the `OutboxBehavior`
  - Remove (cut) the last section of code from the `AddItemHandler` where messages are published and cleared from the collection
  - Add (paste) that code just above the `orderRepository.Store` in the `Invoke` method of the `OutboxBehavior`
  - Notice that now the last call to `orderRepository.Store` can be moved from the `AddItemHandler` to the `OutboxBehavior`. When the message handler finishes, the invocation resumes just after the call to `next()` in the behavior. Move the `Store` call there.
  - Remove the references to the `OrderRepository` from the `AddItemHandler`

Looks better, doesn't it? Event better, it compiles and works. Let's now take care of the last bit of the handler that is related to the deduplication -- the check if a message has been processed.

Remove the `!order.ProcessedMessages.Contains(context.MessageId)` from the handler and move it to the `OutboxBehavior` to guard the calls to `next()` and `orderRepository.Store`.

## It is alive!

The solution works perfectly. You can be proud of yourselves. Let's take a moment to apprieciate that. What we have implemented is in fact the cutting-edge deduplication approach used by multiple commercial and open-source frameworks. That has been a long and tough journey but we made it! From now one we are going to be entering a much less known territory and the algorithms we are going to talk about are not yet available from production-ready tools. But that's good, right? 

But before we go there, there is one last bit... So far we stored our business messages in the outbox. The downside of that is that headers, which are an essential parts of a message, were missing. We'll fix that now.

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















- Open the `OutboxBehavior` class. Notice this class already has some scaffolding code prepared. The `Invoke` code filters out messages that do not carry the order ID on them. This is important because (for now) out generic outbox is going to support only messages addressed to an `Order`. Secondly, there is `InvokeMessageHandler` method that takes care of capturing the messages generated as part of message processing.
- Open the `Order` class. We need to adjust it a bit. Currently it contains two outbox-related properties: `ProcessedMessages` and `OutgoingMessages`. We will replace them with a single property `OutboxState` of type `Dictionary<string, OutboxState>`. The `OutboxState` is a simple class that holds an array of serializable outgoing messages.
- Now the `AddItemHandler` class no longer compiles. Don't worry, we are going to move code from this class to `OutboxBehavior`, line by line.
- First, let's move the code for loading the entity. In case `Load` returns `null`, create a new order and set its ID.
- Next, the `ProcessedMessages.Contains` condition. Let's move it to `OutboxBehavior` and replace `Contains` with `TryGetValue`. The new condition should be `!order.OutboxState.TryGetValue(context.MessageId, out var outboxState))`.
- Inside the `if` body we need to invoke the message handler and store the update value of `Order`
  - To do the first part, invoke our helper method `var messages = await InvokeMessageHandler(context, next);`
  - Then create a new instance of the `OutboxState` containing these messages: `outboxState = new OutboxState {OutgoingMessages = messages.Serialize()};`
  - Finally, set that state in the `Order`: `order.OutboxState[context.MessageId] = outboxState;` and update the database: `await orderRepository.Store(order)`.

- The next part is dispatching of the store operations. This is going to happen regardless of the `if` condition but we need to be careful. If the condition was `false` (we have already seen this message) the `outboxState` can be `null`. We need to account for this by guarding the entire dispatch code with `if (outboxState != null)` condition.
  - Messages to be dispatched need to be deserialized from the outbox state `var toDispatch = outboxState.OutgoingMessages.Deserialize();`
  - Next, they need to be dispatched using a helper method: `await Dispatch(toDispatch, context);`
  - We need to update the state of the order to mark them as dispatched: `order.OutboxState[context.MessageId] = null;`
  - Finally we need to update the order value in the database: `await orderRepository.Store(order)`. 

- The `OutboxBehavior` seems to be ready now but there is one more thing we need to do. The `AddItemHandler` now can't load the `Order` by itself. It needs to work on the `Order` loaded by the behavior.
  - Find the line just before we invoke the message handler and add code to put the loaded `Order` instance on the message handling context: `context.Extensions.Set(order);`
  
- Now we can focus on `AddItemHandler`.
  - Replace the repository usage with retrieving the `Order` from the context: `var order = context.Extensions.Get<Order>();`.
  - Remove the `if` and the curly braces.
  - Remove the `ProcessedMessages.Add` call as it is now handled by setting the `OutboxState` dictionary.
  - Remove the `orderRepository.Store` call. Storing the new state is now handled in the outbox behavior.
  - Replace the `OutgoingMessages.Add` with `await context.Publish`.
  - Remove the dispatching code entirely.
- The code should now look nice and clean.
- Repeat the same steps for the `RemoveItemHandler` class or remove it entirely. We are not going to use it.

- Finally, run the solution and verify if it works
  - Try creating and order and adding two Strawberry items to it quickly. Let's see how the `FirstItemAdded` event is handled.
  - Add another order with one item of meat *pierogi*.

Wow! That was a lot of work. Let's take a moment to celebrate what we achieved. We have build a working implementation of the *Outbox*.

Ok. That's enough. Now let's be a bit more critical. Can you find any problems with this solution?
