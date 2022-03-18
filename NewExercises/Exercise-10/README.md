# Exercise 10: Business ID-based deduplication

Create-type operation can be de-duplicated based on the ID of the entity/aggregate to be created. Add such logic to the order. And test.

- Go to the `SubmitOrderHandler` class and change the `Guid`-based order ID generation strategy with the value of the `CartId` property of the `SubmitOrder` message.
- Run the solution to see the result
- Modify the code of the `SubmitOrderHandler` to discard the message if an order already exists by using `repository.Get` method. Remember to check the `version` part of the return because the `Get` method always returns a non-null item.