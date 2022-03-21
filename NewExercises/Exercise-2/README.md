# Exercise 2 - State-based deduplication

The code in the previous exercise was very naive as it did not prevent duplicate submissions. Such a guard can be seen as a basic business rule:

> Order can't be submitted more than once

This business rule also represents the most basic form of request deduplication. Regardless of how we label it, we need to add code that protects our shopping carts from duplicate submissions.

- Add a boolean flag (property) `Submitted` to the `ShoppingCart` class.
- In the `ApplicationServices`-class, modify the `SubmitOrder` method to check if the cart wasn't already submitted. If so, throw an exception.
- If not, set that property to `true`.
- In the `repository.Put`-method, pass the cart as a parameter to ensure the submitted flag is persisted. This method uses [Cosmos DB's `TransactionalBatch` feature](https://docs.microsoft.com/en-us/azure/cosmos-db/sql/transactional-batch) to ensure that modifications to all passed objects are persisted [atomically](https://en.wikipedia.org/wiki/Atomicity_(database_systems)).

This helped to mitigate the behavior we perceived previously. 
Next, try adding a simulated pause (e.g. via `await Task.Delay(3000)`) right before the `repository.Put` call, to help us simulate concurrent submissions. Now, try the duplicate order submission scenario using two browser tabs. What behavior do you observe?