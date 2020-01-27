# Exercise 8: Deterministic IDs

As you recall, the non-deterministic nature of ID generation made it impossible for the downstream endpoints to de-duplicate messages based on the ID. In this exercise we will attempt to fix the problem of non-deterministic message IDs by changing the ID generation strategy.  

- Use `Utils` class to generate the GUID-like ID based on the hash of the incoming message ID and the name of the processing endpoint
- Modify the handlers of `AddItem` and `RemoveItem` commands to use `PublishWithId` instead of `Publish`
- Test the solution