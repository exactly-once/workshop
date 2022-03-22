NOTE: Starting this exercise, we use automated tests to showcase how the system behaves in various scenarios that can occur in messaging systems.

Our system was extended with new functionality. After an order has been placed, a payment for a given order can be booked or cancelled. So far, the deduplication mechanism depended on the idempotency of the message handling logic. 
Marking the payment as booked, is an operation that has the same observable result, regardless of how many times we execute it. 
Similarly, when we mark the payment as not-booked, we can repeat the operation multiple times without unexpected side effects.

Let's see what happens when some of these messages are reordered:

* Open `IntegrationTests.cs` in the `Test` project and navigate to the `ChangeStatus` test
* Use the `SendInOrder` method to simulate a scenario in which an order is placed, the payment is booked and later cancelled. We want the `BookPayment` command to be duplicated and the duplicate to arrive as the last message:
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
* Run the `ChangeStatus` test and check if the assertion holds. If not, can you tell what's wrong?
* Add a `List<Guid>` property called `ProcessedMessages` to the `Order` entity 
```csharp
 public List<Guid> ProcessedMessages { get; set; } = new List<Guid>();
```
* In the `BookPaymentHandler` and `CancelPaymentHandler`, modify the deduplication logic to use message Ids. At the end of the message processing logic, right before the `Order` is persisted, include the Id of the message being processed in the `ProcessedMessages` collection. At the beginning of the handler, check whether the message already exists in the collection. If so, exit the handler, discarding the message.

What aspect of a message handler is missing in this exercise?
