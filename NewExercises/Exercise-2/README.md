# Exercise 2 - State-based deduplication

The code in the previous exercise was very naive as I did not guard against attempts at duplicate submission. Such guard can be seens as basic business validation

> Order can't be submitted more than once

but it also can be seen as the most basic form of request deduplication. Regardless how we label it, we need to add code that protects our shopping carts from double submission.

- Add a boolean flag (property) `Submitted` to the `ShoppingCart` class.
- In the `ApplicationServices` class modify the `SubmitOrder` method to check if the cart is not submitted before submitting it. If so, throw an exception.
- If not, set that property to `true`.
- In the `repository.Put` call pass the cart as another parameter to ensure the change in the submitted flag is persisted. This method uses Cosmos DB's `TransactionalBatch` feature to make sure that modifications to all passed objects are done atomically.

Did that help? We hope so. Now let's try to break the application again. How about adding a simulated pause (e.g. via `await Task.Delay(3000)`) right before the `repository.Put` call? Can you try the double submission hack using two browser tabs.