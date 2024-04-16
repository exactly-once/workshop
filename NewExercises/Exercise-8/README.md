# Exercise 8 - Automate retries

In the previous exercise we allowed the customer to retry submitting their order in case there is an error. That's a good change. But the system is still far from ideal. Is pushing the burden of handling our system failures on the customer OK? Certainly not.

The solution is based on two observations
- The messaging infrastructure is usually much more reliable (higher availability) than databases. If well maintained, it almost always accepts sent messages.
- The message processing using a durable messaging infrastructure has built-in retry capability.

We are going to create a solution in which the payload of the submit request is encapsulated into a message that is sent to the local queue. The complex business logic of the `SubmitOrder` is moved to a message handler to allow for automatic retries in case of failures.

Let's write some code.

- In the `Messages` project create a new message class `SendSubmitOrder` with two `string` properties: `Customer` and `CartId`.
- In the `Program` class in the section where NServiceBus is configured remove the call to `SendOnly`. We need to make the `WebFrontend` and active endpoint to process the `SendSubmitOrder` messages.
- In the same piece of code make sure the `repository` is available to NServiceBus handlers by adding following code

```c#
endpointConfiguration.RegisterComponents(c =>
  {
      c.AddSingleton(repository);
  });
```

- In the `WebFrontend` project add a handler for the `SendSubmitOrder` message, similar to the `SubmitOrderHandler` in the `Orders` project
  - Remember to implement the `IHandleMessages<SendSubmitOrder>` interface.
  - Add a `repository` parameter of type `Repository` to the constructor and store the value in an instance field
- Move the code from the `SubmitOrder` method to the `Handle` method of the new handler.
  - Replace the parameter references to references to the incoming message
  - Replace the `session.Send` call with `context.Send`
    - Pass an instance of `SendOptions` to the send method. Configure the send options to use immediate dispatch via `sendOptions.RequireImmediateDispatch()` before sending.
- Change the code from the `SubmitOrder` method
  - Remove existing code
  - Add a call to `session.SendLocal` passing an instance of a `SendSubmitOrder` class.

- Does it stil make sense to throw exception when the cart is already marked as submitted and `SendSubmitOrder` is received? Why?
- Why do you think `RequireImmediateDispatch` is needed?

Consider the output of the `Orders` backend application. What did you notice?
