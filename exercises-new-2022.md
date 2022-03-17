### Exercise 1 - a simple web app
 - Shopping cart with items
 - AddItem button to add pierogi
 - Order -> Creates a new entity called Order

Follow up: what happens if you click "Order" twice quickly? Two orders.

### Exercise 2 - deduplicate order processing with a flag

 - Add a flag "Submitted" to the shopping cart
 - Changes the flag to true when creating order - state-based deduplication

- Add property `Submitted` to the `ShoppingCart` class
- In the `ApplicationServices` class modify the `SubmitOrder` method to check if the cart is not submitted before submitting it. If so, throw an exception
- If not, set that property to `true`
- In the `repository.Put` pass the cart as another parameter to ensure the change in the submitted flag is persisted

Follow up: what happens if you click "Order" twice _very_ quickly? Two orders

- In the `ApplicationServices` class modify the `SubmitOrder` and add `Task.Delay(3000)` call before the `repository.Put`. Check again.

### Exercise 3 - optimistic concurrency

- In the `ApplicationServices` class modify the `SubmitOrder` method to include the version properties in the `repository.Put` call
   - the version of the cart is available as the `version` variable
   - pass `null` as the version of the order (creating a new one)
   - hint: the concurrency-friendly `Put` API expects a collection of `(Entity, string)` tuples

### Exercise 4 - make it async - handle a message

- Move the `Order` class from the `WebFrontend` project to the `Orders` project.
- In the `ApplicationServices` class change the type used by the `GetOrders` method from `Order` to `ShoppingCart`. From now on this method will only list shopping carts. Change the name to `GetShoppingCarts`.
- In the Orders project find `SubmitOrderHandler` class. Notice it implements `IHandleMessages<SubmitOrder>` in order to tell the endpoint that it can handle messages of type `SubmitOrder`
- Move the code that creates and saves the order from the `SubmitOrder` method to the `Handle` method of `SubmitOrderHandler`
  - You can now remove the `Task.Delay`
  - Consider logging something at the end of the `Handle` method e.g. `log.Info("Order submitted "+ order.Id);`
  - Remember that in the `SubmitOrder` method you still need to save the cart after the flag is is set
- In the `SubmitOrder` method, after the call to `repository.Put` to save the state of the cart, add code to send the `SubmitOrder` message. Use the `session` field of type `IMessageSession` and its `Send` method. Set the properties of the `SubmitOrder` message based on the shopping cart.

Introduction to messaging - asynchronous processing, distributed systems etc.

 - Order button flips a flag and sends a message and a handler creates the order

Uses a solution similar to the current Ex 14 - after the sync/async boundary.

### Exercide 5 - simulate broker problems

In NServiceBus the appropriate extension point for this task is the `Behavior` class. NServiceBus has message processing pipelines for incoming and outgoing messages. These pipelines are composed of `Behaviors`. Each behavior can execute arbitrary code and pass invocation to behaviors that are further down the pipeline. Here's an example behavior:

```
class MyBehavior : Behavior<IOutgoingLogicalMessageContext> //T defines in which part of the pipeline the behavior is injected
{
  public override async Task Invoke(IOutgoingLogicalMessageContext context, Func<Task> next)
  {
    //Any code can be executed here

    //calling next() passes the control to the next behavior
    await next();
    //after all the behaviors further down the pipeline complete, the next() returns

    //Any code can be executed here
  }
}
```

Create a behavior in the outgoing pipeline that duplicates the send invocation
- In the `WebFrontend` project create a new class derived from `Behavior<IOutgoingLogicalMessageContext>`
- In the `Invoke` method call `await next()` to create a behavior that does nothing but just forwards the invocation
- In the `Program` class of `WebFrontend` project register the behavior with `EndpointConfiguration` via `Pipeline.Register` API (e.g. after the call to `endpointConfiguration.SendOnly()`)
- Run the solution to check if messages continue to flow. Put a breakpoint in the new behavior to verify that it is invoked
- In the behavior class add an instance field `failed` to ensure that only the first message triggers the failure
- Add code in the behavior that checks if `failed` flag is not set. If it is not, set the flag to `true` and throw new `Exception`. This will ensure that the first attempt to send a message after the web application is started is always going to fail.

Now try placing the order.

Explanation: you can go back and see the cart on the list but you can't re-submit it because it is already marked as submitted.


### Exercise 6 - change the order of operations

- Go to the `ApplicationServices` class and the `SubmitOrder` method and check if the system can handle the broker failures gracefully.
- Go on add add few more orders.

Follow up:

What you have seen are ghose messages. These are messages that carry the state that has not been persisted. Ghost messages are as bad as missing messages. We need to solve this problem.

### Exercise 7 - re-send if in doubt

- Go to the `ApplicationServices` class and change the logic to do the following:
  - If the cart is not yet submitted, set the `Submitted` flag and save the cart
  - Send the `SubmitOrder` message regardless if the cart has been submitted before or has just been submitted.
- The new logic should now throw exceptions. Instead, if the `SubmitOrder` is invoked multiple times (e.g. when the previous attempt failed), it should re-send the message.
- Check what are the consequences of this behavior to the `Orders` service.

Follow up:

What we have just experienced is sender-side duplication. In order to avoid both lost and ghost messages we need to use the at-last-once approach to sending outgoing messages. The endpoint that receives these messages will have to deal with these duplicates. But before we get there, we want to take a look at another source of duplication.

### Exercise 8: Re-send automatically

- In the `Messages` project create a new message class `SendSubmitOrder` with two `string` properties: `Customer` and `CartId`.
- In the `Program` class in the section where NServiceBus is configured remove the call to `SendOnly`. We need to make the `WebFrontend` and active endpoint to process the `SendSubmitOrder` messages.
- In the same piece of code make sure the `repository` is available to NServiceBus handlers by adding following code

```c#
endpointConfiguration.RegisterComponents(c =>
  {
      c.RegisterSingleton(repository);
  });
```

- In the `WebFrontend` project add a handler for the `SendSubmitOrder` message, similar to the `SubmitOrderHandler` in the `Orders` project
  - Remember to implement the `IHandleMessages<SendSubmitOrder>` interface.
  - Add a `repository` parameter of type `Repository` to the constructor and store the value in an instance field
- Move the code from the `SubmitOrder` method to the `Handle` method of the new handler.
  - Replace the parameter references to references to the incoming message
  - Replace the `session.Send` call with `context.Send`
- Change the code from the `SubmitOrder` method
  - Remove existing code
  - Add a call to `session.SendLocal` passing an instance of a `SendSubmitOrder` class.

### Exercise 9: Duplicates on the receiver (lock timeout)

The solution now uses the ASQ transport and there. Put the delay in the Process order handler.

### Exercise 10: Business ID-based deduplication

Create-type operation can be de-duplicated based on the ID of the entity/aggregate to be created. Add such logic to the order. And test.

- Go to the `SubmitOrderHandler` class and change the `Guid`-based order ID generation strategy with the value of the `CartId` property of the `SubmitOrder` message.
- Run the solution to see the result
- Modify the code of the `SubmitOrderHandler` to discard the message if an order already exists by using `repository.Get` method.

### Exercise 11

Predictable automated tests for messaging systems

### Exercise 12

This and couple of following exercises use automated tests for show how our system behaves in various scenarios that might happen in messaging systems.

Our system has been extended with new functionality. After order has been placed, we can book a pyment for a given order or cancel a payment that has been already booked. Let's see what happens when some of these messages get reordered:

* Open `IntegrationTests.cs` in the `Test` project and naviage to `ChangeStatus` test
* Use `SendInOrder` utility method to simulate scenario in which oder is placed, payment is booked and later cancelled but the `BookPayment` command in duplicated and the duplicate arrives as the last message:
```csharp
await SendInOrder(new IMessage[]
  {
      submitOrder,
      bookPayment,
      cancelPayment,
      bookPayment
  }
);
``` 
* Run `ChangeStatus` test and check if the assertion holds
* Add `List<Guid>` property to `Order` enity called `ProcessedMessages`
* Use `ProcessedMessages` and `CartId` value in the `BookPayment` command to track processed messages and avoid re-processing duplicates


### Exercise 11, 12 and 13 - customer status policy

Using a different solution that only has the policy endpoint. Using the acceptance testing framework.

 - SubmitOrder -> OrderSubmitted
   - Idempotent operations not idempotent when re-ordering -> use message IDs
   - ID-based deduplication only good if IDs are stable
   - Deterministic state

### Summary

 - State-based deduplication at the boundary of the system - requires optimistic concurrency
 - ID-based de-duplication only good when creating entities 
 - Idempotent operations are not idempotent when re-ordering is allowed
 - Message-id based deduplication requires deterministic IDs
 - No deduplication method is correct when the state of the object is allowed to change between the duplicated messages

### Exercise 14: Outbox (previously exercise 12 - generic outbox)

Back to a simple solution for exericese 10.

### Exercise 15: Outbox with Inbox (previously exerice 13 - inbox)

