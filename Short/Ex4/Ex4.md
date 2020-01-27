# Exercise 4: Simulate broker problems

In this exercise we are going to continue using principles of *chaos engineering* to add another chaos monkey. This time the monkey is going to simulate broker failure for a specific type of `Item` -- `QuarkAndPotatoes`.

- Create a behavior in the outgoing pipeline that fails sending
 - In the `Orders` project create a new class derived from `Behavior<IOutgoingLogicalMessageContext>`. Call it `BrokerErrorSimulatorBehavior`.
 - In the `Invoke` method call `await next()` to create a behavior that does nothing but just forwards the invocation
 - In the `Program` class of `Orders` endpoint register the behavior with `EndpointConfiguration` via `Pipeline.Register` API
- Run the solution to check if messages continue to flow. Put a breakpoint in the new behavior to verify that it is invoked

- Add an instance field `failed` to ensure that only the first message triggers the failure
- Add code in the behavior that inspects `context.Message.Instance`, checks it is an instance of `ItemAdded`, it is of type `QuarkAndPotatoes` and `failed` flag is not set. If all these are true, set the flag to `true` and throw new `Exception`.
