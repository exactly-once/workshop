# Exercide 5 - Simulate problems

In this exercise we are going to use the principles of *chaos engineering* to ensure our system is robust. Instead of relying on pure chance for testing the failure modes of our system, we are going to build into a *chaos monkey* -- a piece of code that is going to introduce a certain category of anomalies into our system **on purpose**. This will allow us to write code that handles these types of anomalies when they occur in production (according to Murphy's laws it is going to happen on Friday afternoon just before your long-planned vacation).

In NServiceBus the appropriate extension point for this task is the `Behavior` class. NServiceBus has message processing pipelines for incoming and outgoing messages. These pipelines are composed of `Behaviors`. Each behavior can execute arbitrary code and pass invocation to behaviors that are further down the pipeline. Here's an example behavior:

```
class MyBehavior : Behavior<IOutgoingLogicalMessageContext> //T defines in which part of the pipeline the behavior is injected
{
  public override async Task Invoke(IOutgoingLogicalMessageContext context, Func<Task> next)
  {
    //Any code can be executed here

    //calling next() passes the control to the next behavior
    await next();
    //after all the behaviors further down the pipeline complete, the next() returns

    //Any code can be executed here
  }
}
```

Create a behavior in the outgoing pipeline that duplicates the send invocation
- In the `WebFrontend` project create a new class derived from `Behavior<IOutgoingLogicalMessageContext>`
- In the `Invoke` method call `await next()` to create a behavior that does nothing but just forwards the invocation
- In the `Program` class of `WebFrontend` project register the behavior with `EndpointConfiguration` via `Pipeline.Register` API (e.g. after the call to `endpointConfiguration.SendOnly()`)
- Run the solution to check if messages continue to flow. Put a breakpoint in the new behavior to verify that it is invoked
- In the behavior class add an instance field `failed` to ensure that only the first message triggers the failure
- Before the `next()` call add code in the behavior that checks if `failed` flag is not set. If it is not, set the flag to `true` and throw new `Exception`. This will ensure that the first attempt to send a message after the web application is started is always going to fail.

Now try placing the order and see what happens. Has the backend received the message? What does the customer think about their pierogi order?