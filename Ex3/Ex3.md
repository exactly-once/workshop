# Exercise 3: Simulate database problems

In this exercise we are going to continue using principles of *chaos engineering* to add another chaos monkey. This time the monkey is going to simulate database connection failure when committing the transaction for a specific type of `Item`. The simulation will be done using an EntityFramework validation logic.

- In the `Item` entity class add a range validator `[Range((int)Filling.Meat, (int)Filling.QuarkAndPotatoes, ErrorMessage = "Database failure")]` to simulate database problem whenever trying to create an item that has `QuarkAndPotatoes` filling type
- Run the solution
