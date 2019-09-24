# Exercise 7: ID-based de-duplication

In this exercise we are going to fundamentally alter the way we process messages. Instead of relying on the idempotence of data structures used, we will employ unique message IDs. Because we have multiple handlers, we will attempt to create a re-usable component that can de-duplicate any type of message

- Add a `bool Processed` property to `OrdersDataContext` to indicate to the handler that business logic has already been executed
- Add an entity class `ProcessedMessage` with a single `string` property `MessageId`
- In the `OrdersDataContext` ensure the new entity is mapped and has a corresponding entity collection
- Create a behavior in the incoming pipeline that de-duplicates based on the message ID
  - Create a class dervived from `Behavior<IIncomingLogicalMessageContext>` and implement the `Invoke` method
- In the `Program` class of `Orders` endpoint register the behavior with `EndpointConfiguration` via `Pipeline.Register` API
- In the `Invoke` method:
  - Create an instance of `OrdersDataContext`
  - Open a transaction within a using statement
- In that using statement implement the de-duplication logic
  - Try load a `ProcessedMessage` entity with `MessageId` equal to the ID of current message being processed (available via `context.MesssageId`)
  - If there is no such entity, create a new one and add it to the `ProcessedMessages` entity collection of the data context
  - If there is one, set the data context `Processed` property to `true`
  - Flush changes to database by calling `SaveChangesAsync`
  - Add the instance of `OrdersDataContext` to the context of message handling by calling `context.Extensions.Set()`
  - Invoke the remainder of the pipeline by calling `await next()`
  - Flush changes to database by calling `SaveChangesAsync`
- Modify the `AddItem` and `RemoveItem` handlers
  - Instead of creating a data context, retrieve it from the message processing context via `context.Extensions.Get<OrdersDataContext>()`
  - Execute the business logic if `Processed` property is set to `false`
  - If `Processed` is set to `false` then re-publish the outgoing event
  - If `Processed` is set to true, publish the outgoing event only if an item has actually been added or removed
    - When trying to add and an item is already present, do not publish an event
    - When trying to remove and an item does not exist, do not publish an event 
- Log message ID in the `Billing` endpoint handlers
  - Add `Message {context.MessageId}:` in front of the log statement format string
- Run the solution and add an `Item` of type `Meat`