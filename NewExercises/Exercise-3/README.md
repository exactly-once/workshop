# Exercise 3 - Optimistic concurrency

What we've observed in the previous exercise is the effect of a lack of [concurrency control](https://en.wikipedia.org/wiki/Concurrency_control) in our application. Concurrency control is the basis of all consistency control techniques that we will encounter during the workshop.

The modification of the shopping cart is based on a *view* (or *snapshot*) that was obtained sometime in the past. The shopping cart might have changed between the time when the *snapshot* was taken and the time when the changes submitted, which is why consistency control is required.

Concurrency control is essential in any distributed system in which data modifications are applied in a different process from the one that keeps the data. This applies to *any* modern application unless it is purely based on stored procedures. Even in the latter case, depending on the transaction isolation level, concurrency control might be necessary.

Let's add optimistic concurrency control - implemented in CosmosDB through version numbers (`ETag`) passed to the put request. If the version is included, the update will only succeed when the version of the document in the database matches the version included in the request. If not, the whole `TransactionalBatch` is rejected.

- In the `ApplicationServices` class, modify the `SubmitOrder` method to include the version properties in the `repository.Put` call
   - the version of the cart is already available as the `version` variable
   - pass `null` as the version of the order (can you explain why?)
   - hint: the concurrency-friendly `Put` API expects a collection of `(Entity, string)` tuples
