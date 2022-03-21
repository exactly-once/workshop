# Exercise 5 - Monkeys of Chaos

In this exercise we are going to use the principles of [chaos engineering](https://en.wikipedia.org/wiki/Chaos_engineering) to ensure our system is robust. Instead of testing the behavior of our system in different failure modes based on pure chance, we are going to build a *chaos monkey* -- a piece of code that is going to introduce a certain series of anomalies into our system **on purpose**. This will allow improve the system's ability to cope with such anomalies when they occur in production (according to [Murphy's law](https://en.wikipedia.org/wiki/Murphy%27s_law), this will happen on Friday afternoon just before your long-planned vacation).

In NServiceBus, the [appropriate extension point](https://docs.particular.net/nservicebus/pipeline/manipulate-with-behaviors) for these types of concerns, is the `Behavior` class. NServiceBus handles incoming and outgoing messages by passing them through [processing pipelines](https://docs.particular.net/nservicebus/pipeline/) composed of `Behaviors`. Each behavior can execute arbitrary code and passes the invocation to behaviors further down the pipeline. 

Here's an example behavior:

```
class MyBehavior : Behavior<IOutgoingLogicalMessageContext> // T defines in which part of the pipeline the behavior is injected
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

Create a behavior in the outgoing pipeline that duplicates the send invocation:
- In the `WebFrontend` project create a new class derived from `Behavior<IOutgoingLogicalMessageContext>` and implement its members
- In the `Invoke` method, call `await next()` to create an empty behavior that just forwards the invocation
- In the `Program` class of the `WebFrontend` project, register the behavior on the `endpointConfiguration`-variable using the `Pipeline.Register`-API (e.g. after the call to `endpointConfiguration.SendOnly()`)
- Run the solution to check if messages continue to flow. Place a breakpoint in the new behavior to verify that it is invoked
- In the behavior class, add an instance field named `failed` to ensure that only the first message triggers the failure
- Before the `next()` call, add code that checks whether the `failed` flag is set. If it is not, set the flag to `true` and throw a new `Exception`. This will ensure that the first attempt to send a message after the web application is started is always going to fail.

Now try placing the order and observe what happens. Has the backend received the message? What does the customer believe happened to their pierogi order?
