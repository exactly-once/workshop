# Exercise 5: Simulate database problems

In this exercise we are going to continue using principles of *chaos engineering* to add another chaos monkey. This time the monkey is going to simulate database connection failure when committing the transaction for a specific type of `Item`.

- In the `OrderRepository` class in the `Store` method check if a given order contains item of type `SwissCheese`. If so, throw `DatabaseErrorException` to simulate database problems.
- Run the solution
  - What happened?
  - Go to [follow up](https://github.com/exactly-once/workshop/blob/master/Exercise-5/follow-up.md) section to continue
