# Exercise 12: Generic outbox

In the previous exercise we implemented the Outbox pattern inline in the handler of the `AddItem` message. While it did solve our problem, it is not ideal from the code reuse perspective. Who would like to have the same code copied over and over again? In this exercise we are going to extract that piece of code and make it more generic. In order to achieve this we will use the *behavior* extension system of NServiceBus; the same one that we previously used to simulated various failure conditions.

- Open the `OutboxBehavior` class. Notice this class already has some scaffolding code prepared. The `Invoke` code filters out messages that do not carry the order ID on them. This is important because (for now) out generic outbox is going to support only messages addressed to an `Order`. Secondly, there is `InvokeMessageHandler` method that takes care of capturing the messages generated as part of message processing.
- Open the `Order` class. We need to adjust it a bit. Currently it contains two outbox-related properties: `ProcessedMessages` and `OutgoingMessages`. We will replaced them with a single property `OutboxState` of type `Dictionary<string, OutboxState>`. The `OutboxState` is a simple class that holds an array of serializable outgoing messages.

If for a given value of message ID the `OutboxState` dictionary contains a non-null value, the messages have not been dispatched. If it contains `null` then that message have been processed and outgoing messages dispatched. If it does not contain that value, the message has not been processed.

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