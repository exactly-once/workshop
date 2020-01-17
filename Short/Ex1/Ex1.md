# Exercise 1: Idempotent business logic

In the first exercise we are going to attempt to implement an idempotent message handler in the `Orders` endpoint. This endpoint already handles `CreateOrder` messages generated when the customer browses to the new order page. Now it is also going to handle `AddItem` messages. In this version (Minimum Viable Product) of the system the customers can add only one item of a given type to a single order. The engineering team recognizes immediately that this business requirement turns the `Order` into a set of `Item` types. For each possible type, any given order either contains it or not. Adding a given type of `Item` twice is equivalent of adding it once as set *union* and *intersection* operations are idempotent. As part of processing the `AddItem` message, publish an event called `ItemAdded` to notify other interested endpoints.

- In the Orders project find `AddItemHandler` class. Notice it implements `IHandleMessages<AddItem>` in order to tell the endpoint that it can handle messages of type `AddItem`
- Inside the `Handle` method:
  - Load the `Order` entity using the repository
  - Create a new `OrderLine` object and add it to the order's collection
  - Publish an `ItemAdded` event
  - Persist the changes to the `Order` entity using the repository
- Test the logic by running a code and creating an order with a couple of items