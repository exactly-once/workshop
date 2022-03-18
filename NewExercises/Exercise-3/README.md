# Exercise 3 - Optimistic concurrency

What you have seen in the previous exercise is the effect of lack of any concurrency control in our application. Concurrency control is the basis of all other, more advanced, consistency control measure we will encounter during the workshops.

Consistency control is needed because the modification of the shopping cart is based on a *view* (or *snapshot*) of that cart that has been obtained some time earlier. The shopping cart might have changed between the time when the *snapshot* was taken and the time when the changes are to be applied.

Concurrency control is essential in any distributed system in which modifications to the data are computed in a different process from the one that keeps the data. This pretty much means *any* modern application unless it is based purely on stored procedures. And even in that case, depending on the transaction isolation level, concurrency control might be necessary.

Let's add optimistic concurrency control to our application. Fortunately Cosmos DB offers a way to include the version (or `etag`) in the update request. If the version is included, the update succeeds only if the version of the document in the database matches the version included in the request. If not then the whole `TransactionalBatch` is rejected.

- In the `ApplicationServices` class modify the `SubmitOrder` method to include the version properties in the `repository.Put` call
   - the version of the cart is already available as the `version` variable
   - pass `null` as the version of the order (can you explain why?)
   - hint: the concurrency-friendly `Put` API expects a collection of `(Entity, string)` tuples