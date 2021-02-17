# Exercise 8: ID-based de-duplication

In the previous exercise, we've seen that idempotent data structures do not guarantee the correctness of the behavior if messages can be re-ordered in transit. In this exercise, we are going to solve this problem by fundamentally altering the way we process messages. Instead of relying on the idempotence of data structures, we will employ synthetic message IDs. 

- Add a `ProcessedMessages` property to `Order` that contains a list of IDs of processed messages (each ID is a string)
- In `AddItemHandler` and `RemoveItemHandler` replace the filling-based de-duplication check with one based on processed messages
  - message handling context (`IMessageHandlerContext`) has a property containing the message ID
  - check if the message ID is already in the `ProcessedMessages` collection. If so, the message is a duplicate

- Before persisting changes done to `Order` ensure that the ID of the current message is added to the `ProcessedMessages` collection
- Leave the message publishing code as-is
