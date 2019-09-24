# Exercise 2: Simulate message duplication

In this exercise we are going to use principles of *chaos engineering* to add a chaos monkey that duplicates all outgoing messages. We are going to use NServiceBus framework for messaging but any other similar framework offers similar extension points.

In NServiceBus the extension point is the `Behavior` class. NServiceBus has message processing pipelines for incoming and outgoing messages. These pipelines are composed of `Behaviors`. Each behavior can execute arbitrary code and pass invocation further to behaviors that are further down the pipeline. Here's an example behavior:

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

- Create a behavior in the outgoing pipeline that duplicates the send invocation
  - In the `Frontend` project create a new class derived from `Behavior<IOutgoingLogicalMessageContext>`
  - In the `Invoke` method call `await next()` to create a behavior that does nothing but just forwards the invocation
  - In the `Program` class of `Frontend` endpoint register the behavior with `EndpointConfiguration` via `Pipeline.Register` API
  - Run the solution to check if messages continue to flow. Put a breakpoint in the new behavior to verify that it is invoked
  - Add another `await next()` call to the behavior to create duplicate outgoing messages
- Run the solution