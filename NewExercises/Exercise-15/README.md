# Exercise 15: Generic outbox

In the previous exercise, we've implemented the Outbox pattern inline in the handler of the `AddItem` message. While it did solve our problem, it is not ideal from the code reusability perspective. 
Who wants the same code duplicated everywhere? In this exercise we will extract that piece of code and make it more generic. In order to achieve this we will use the *behavior* extension system of NServiceBus; the same one that we previously used to simulate various failure conditions.

Before we start coding, let's open the completed exercise 14 and the solution for the exercise 15 side-by-side. Go to the `BookPaymentHandler` and `AddItemHandler`. Take a look at the code. It looks almost exactly the same, right? That's not by coincidence. Both handlers execute different business logic but have the same structure. That's an opportunity for code sharing, which is the point of this exercise.

Now let's get our hands dirty.

- Open the `OutboxBehavior` class. By now, you should be familiar with behaviors. They provide a framework to express cross-cutting concerns in NServiceBus. This behavior doesn't do anything right now, but in the course of this exercise we'll extend it.
- In the `OutboxBehavior`, before passing the invocation further on line 27, load the order from the repository and add it to the context.
  - Load the order based on the `OrderId` property of the `orderMessage`
  - Put it in the handling context: `context.Extensions.Set(order);`
- Persist the changes by calling `orderRepository.Store` after the call to `next()` (calling `next()` invokes the message handler)
- Replace all usages of repository in the `AddItemHandler` with usages of the `Order` instance managed by the `OutboxBehavior`
  - Replace the repository usage by retrieving the `Order` from the context: `var order = context.Extensions.Get<Order>();`
  - Remove the second call to `orderRepository.Store` as it is handled by the behavior
- Run the code

With this change, we moved most of the code responsible for loading and storing the entity to the `OutboxBehavior` and the handler can focus on the actual business logic. But there is some stuff left so let's continue.

- Move the code responsible for publishing messages to the `OutboxBehavior`
  - Remove (cut) the last section of code from the `AddItemHandler` where messages are published and cleared from the collection
  - Add (paste) that code just below the `orderRepository.Store` in the `Invoke` method of the `OutboxBehavior`

Looks better, doesn't it? Even better, it compiles and works. Now, let's take care of the bits of code in the handler that's' related to deduplication -- the check if a message has been processed.

Remove the `!order.ProcessedMessages.Contains(context.MessageId)` from the handler and move it to the `OutboxBehavior` to guard the calls to `next()` and `orderRepository.Store`. Voila!

## It is alive!

The solution works perfectly. You can be proud of yourselves. Let's take a moment to appreciate that. What we have implemented is in fact the cutting-edge deduplication approach used by multiple commercial and open-source frameworks. That has been a long and tough journey but we made it! Moving forward, we're going to enter a much less known territory and the algorithms we are going to talk about are not yet available in production-ready tools. But that's good, right? 