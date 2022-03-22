# Exercise 10: Primary key-based deduplication

Create-type operations can be deduplicated based on the ID of the entity/aggregate to be created. 

Try to add such deduplication logic to the order and test the behavior.

- In the `SubmitOrderHandler` class, change the `Guid`-based order ID generation strategy with the value of the `CartId` property of the `SubmitOrder` message.
- Run the solution to see the result
- Modify the code of the `SubmitOrderHandler` to discard the message if an order already exists by using `repository.Get` method. Remember to check the `version` because the `Get` method always returns a non-null item.