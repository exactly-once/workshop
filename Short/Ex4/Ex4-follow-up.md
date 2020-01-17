# Exercise 4: Simulate broker problems

Follow up:
- Modify the handler for the `AddItem` command so that:
  - The business logic (adding a new `Item` to the collection) and persisting state (`Store`) are executed only if message is not considered a duplicate
  - `Publish` is executed regardless if a message seems to be a duplicate
- Run the solution to make sure that `Billing` receives a notification when `Item` of type `QuarkAndPotatoes` is added
- Unfortunately the outgoing message is never published because each time we try, the broker fails
- Mitigate the problem by introducing an instance field `bool failed` to `BrokerErrorSimulatorBehavior` to ensure the exception is throw only on the first attempt
  - set the flag to `true` before throwing exception
  - throw exception only if the flag is `false`
