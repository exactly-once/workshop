# Exercise 15: Out-of-document outbox - part 1

In this exercise we are going to attempt to minimize the footprint of the outbox algorithm. The previous implementation required to have the outbox state dictionary as part of the entity. This approach might not be feasible for databases that impose strict limits on entity size (e.g. Cosmos DB). Let's start with a bold statement:

> We can make the algorithm work based only on a single `string` field in the entity.

As a first step towards that bold goal, let's try to remove the need to store the bulky outbox state within the entity. We will use an external outbox store. The definition and the implementation of that store is already part of the codebase.

First, we'll introduce the concept of *transaction ID*. Transaction is an attempt at processing a message. We are going to store the outbox state documents under transaction ID and the same transaction ID will be persisted as part of the entity.

Go to the `Entity` class and remove the `OutboxState` dictionary. Add a new property called `TransactionIds` as `Dictionary<string, string>`.

Generate a new transaction ID as a first thing inside the *is not processed yet* condition: `transactionId = Guid.NewGuid().ToString();`. Replace `entity.OutboxState[context.MessageId]` with:
 - Storing the actual value: `await outboxStore.Put(transactionId, outboxState)`.
 - Assigning the transaction ID: `entity.TransactionIds[context.MessageId] = transactionId;` 

Now let's update the condition. It needs to be based on the transaction ID dictionary. You probably noticed that the bottom part of the method won't work because the `outboxState` property is not assigned if the transaction ID has been found in the dictionary.

Add the `else` branch loading the outbox state by transaction ID: `outboxState = await outboxStore.Get(transactionId);`.

In the bottom part itself we need to replace the outbox state cleanup with transaction ID dictionary cleanup. We also need to remove the outbox state from the store. It is safe to do it right after dispatching the messages.

Now let's focus on the top part. The case when an inbox entry exists needs to be adjusted to use the transaction ID dictionary.

Finally take a look again at the bottom part where we dispatch messages and clean up the outbox. These two operations create an opportunity for a partial failure case. How should we handle it?