# Exercise 1: Idempotent business logic

In the first exercise we are going to attempt to implement an idempotent message handler in the `Orders` endpoint. This endpoint already handles `CreateOrder` messages generated when the customer browses to the new order page. Now it is also going to handle `AddItem` messages. In this version (Minimum Viable Product) of the system the customers can add only one item of a given type to a single order. The engineering team recognizes immediately that this business requirement turns the `Order` into a set of `Item` types. For each possible type, any given order either contains it or not. Adding a given type of `Item` twice is equivalent of adding it once as set *union* and *intersection* operations are idempotent. As part of processing the `AddItem` message, publish an event called `ItemAdded` to notify other interested endpoints.

- Create a unique index on the `Item` in such a way that the items or a given order form a set (there is at most one item of a given type associated with a single order)
  - Use `[Index]` attributes on properties of `Item` entity class
- Test that processing more than one `AddItem` command with the same type results in a constraint violation error
- Write code that detects a duplicate `AddItem` message and ignores it to prevent error escalation
- Write code that publishes the `ItemAdded` endpoint