# Exercise 4: Simulate broker problems

Follow up:
- Modify the handler for the `AddItem` command so that:
  - The business logic (adding a new `Item` to the collection) and persisting state (`SaveChanges`) are executed only if message is not considered a duplicate
  - `Publish` is executed regardless if a message seems to be a duplicate
- Run the solution to make sure that `Billing` receives a notification when `Item` of type `QuarkAndPotatoes` is added
