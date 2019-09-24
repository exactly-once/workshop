# Exercise 9: Even more chaos

In this exercise we will add even more chaos to test our solution against yet another failure mode. So far the simulated broker failures when trying to send messages. This time we will modify the broker failure simulation behavior to simulate failure when acknowledging processing of a received message.
- Change the `T` in the broker failure simulation behavior to `IIncomingLogicalMessageContext`
- Now you can access the incoming message simply via `context.Message.Instance`
- Add delay of 10 seconds before throwing an exception via `Task.Delay`
- To test, quickly issue two `AddItem` commands with a type that triggers the broker failure simulation (`QuarkAndPotatoes`)