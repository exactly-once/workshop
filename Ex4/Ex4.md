# Exercise 4: Simulate broker problems

In this exercise we are going to continue using principles of *chaos engineering* to add another chaos monkey. This time the monkey is going to simulate broker failure for a specific type of `Item` -- `QuarkAndPotatoes`.

- Create a behavior in the outgoing pipeline that fails sending
 - In the `Orders` project create a new class derived from `Behavior<IOutgoingLogicalMessageContext>`
 - In the `Invoke` method call `await next()` to create a behavior that does nothing but just forwards the invocation
 - In the `Program` class of `Orders` endpoint register the behavior with `EndpointConfiguration` via `Pipeline.Register` API
 - Run the solution to check if messages continue to flow. Put a breakpoint in the new behavior to verify that it is invoked
