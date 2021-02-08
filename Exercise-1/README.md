# Exercise 1: Handling a message

In the first exercise we are going to attempt to implement a message handler in the `Orders` endpoint. This endpoint already handles `CreateOrder` messages generated when the customer browses to the new order page. Now it is also going to handle `AddItem` messages. As part of processing the `AddItem` message, publish an event called `ItemAdded` to notify other interested endpoints.

- In the Orders project find `AddItemHandler` class. Notice it implements `IHandleMessages<AddItem>` in order to tell the endpoint that it can handle messages of type `AddItem`
- Inside the `Handle` method:
  - Load the `Order` entity using the `OrderRepository`
  - Create a new `OrderLine` object and add it to the order's collection
  - Publish an `ItemAdded` event
  - Persist the changes to the `Order` entity using the repository
- Test the logic by running a code and creating an order with a couple of items
