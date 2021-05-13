## Conversation based integration tests

When writing integration tests for message-based systems it's common to make assertions on the results of the whole conversation and not the initial command alone. This part of the tutorial shows how to instrument message handling endpoints so that it's possible for the testing logic to run assertions only after all messages in the conversation have been processed. 

### Goal

The goal of this exercise is to write a single integration test that depends on the result of processing the last message in a conversation. The conversation starts with `PlaceOrder` command that has a 1 in 20 chance of triggering the final `FinalizeOrder` command or re-sending the same command with `1` seconds delay:

```csharp
if (new Random().Next(0, 20) == 0)
{
    var options = new SendOptions();
    options.DelayDeliveryWith(TimeSpan.FromSeconds(10));

    await context.Send(message, options);
}
else
{
    await context.SendLocal(new FinalizeOrder{Id = message.Id});
}
```

This, in turn, causes flakiness in the sample integration test. Note that the test is being executed 25 times.

```csharp
[Test]
[Repeat(25)]
public async Task PlaceOrder()
{
    var message = new PlaceOrder {Id = Guid.NewGuid()};

    await endpoint.Send(message);

    Assert.Contains(message.Id, store.PlacedOrders, "PlaceOrder command should result in order record being stored in the OrderStore");
}
```

### Step 1

Can we solve the problem with a simple patch? Can we add `Task.Delay` in our test to make it pass consistently and not make it take a couple of minutes to pass?

### Step 2

Let's add behavior to the message processing pipeline in our endpoint so that for every incoming message and all messages that are generated we capture their identifiers and sent this data off to a dedicated queue for further processing using `TracingBehavior`:

```csharp 
 (endpoint, store) = await Program.StartEndpoint(c =>
{
    c.Pipeline.Register(new TracingBehavior(), "Traces input-output messages");
});
```

TASK: Add a missing piece of logic to the `TracingBehavior` to capture outgoing message identifiers in the `OutgoingMessageIds` property of the `TracingMessage`. Run the test in the `Debug` mode to make sure the data is being captured.

### Step 3

Tracing messages sent to the `trace` queue will be processed by a dedicated endpoint encapsulated in the `Tracer` class. 

TASK: Create an instance of the `Tracer` class in the `Setup` method of the test and make sure it's properly clean-up in the `Cleanup` 

### Step 4

`Tracer` provides logic to setup conversation tracking and later to wait until the conversation finishes. In order, to set up, the conversation one needs to call the `Prepare` method which returns `conversationId` and `SendOptions` tuple.

TASK: Extend the test code by calling the `tracer.Prepare` and `tracer.WaitUntilFinished` to make sure that test asserts are called at the right time.
