# Exercise 5: Allow removal of items

In this exercise we are going to extend the system (because of the public demand) with the feature to remove an `Item` from an `Order` while the order is not yet submitted. We will add the `RemoveItem` command that will be handled by the same endpoint as `AddItem` command. Because the `Order` is represented as a set, the `RemoveItem` operation is idempotent by definition and does not require any attention.

- In the `Messages` project add a new message type `RemoveItem` with the same properties as `AddItem`
- In the `Messages` project add a new message type `ItemRemoved` with the same properties as `ItemAdded`
- In the `Frontend` endpoint add code for sending `RemoveItem` commands:
  - Add a regular expression for recognizing a `remove <type> from <order>` commands
  - In the `while (true)` loop add a branch for matching the new expression, parsing the data and sending a `RemoveItem` command
- In the `Orders` endpoint add a new class that implements `IHandleMessages<RemoveItem>`
  - You can copy the handler for `AddItem` and modify the code so that the business logic removes an item of a given type if present
- In the `Billing` endpoint add a new class that implements `IHandleMessages<ItemRemoved>`
  - You can copy the handler for `ItemAdded` and modify the log statement
- Run the solution and try adding and removing some items