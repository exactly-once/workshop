# Exercise 18: Inbox

In the previous exercise we have implemented a generic version of the Outbox pattern. We quickly discussed its downsides and agreed that we can do better. In this exercise we will introduce a concept of Inbox as a shared storage of deduplication information.

Fortunately for us, the changes won't be big.
 - First, notice that the `OutboxBehavior` class has an additional field -- the `inboxStore`. As discussed, messages that have been completely processed should have entries in that store.
 - Let's add the code that checks the inbox store. Where should we insert this code? To check the inbox call `HasBeenProcessed` method passing the message ID.

The whole middle section of the algorithm remains unchanged. Let's take a look at the bottom part. Where should we insert the `MarkProcessed` call to mark add an entry to the inbox?

Now let's focus on the cleanup. The goal was to avoid holding on to too many data inside the entity. To achieve it we need to replace the `OutboxState[context.MessageId] = null` code with simple `OutboxState.Remove(context.MessageId)`.

Now take a look at the `outboxState != null` condition. Do we still need it?

Finally let's imagine a scenario in which the code fails just after `MarkProcessed`. How do we clean up the outbox state in that case?

