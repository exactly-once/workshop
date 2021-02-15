# Outbox

What we have just experienced showed us that we were missing one critical thing since the very beginning of our journey. We didn't really pay much attention to how we are generating the outgoing messages. It seemed quite obvious that processing an `AddItem` command should result in an `ItemAdded` event. We were (at least some of us, maybe) a bit surprised when we realized that these events have to be given deterministic IDs but that was expected to do the trick. To our surprise it did not solve the problem entirely.

### Re-publish but what?

Remember when we discussed the introduction of message IDs? We stated that we still need to remember to re-publish any outgoing messages in case we suspect a duplicate (as it is indistinguishable from a failure in dispatching outgoing messages). What we didn't focus is how do we know what messages should we send out.

### First-time processing

In the logic that is executed when processing a message for the first time there is an `if` statement that ensures that the event is only published when the state change is actually applied. If no state is changed (e.g. when trying to add an item of a type that already exists), no event is published. This way the downstream endpoint can, by counting `ItemAdded` and `ItemRemoved` messages have an accurate counters for number of items in each order.

### Duplicate suspect

That's fine but what about the case when the message is already marked as processed? We execute the other branch where we unconditionally publish the `ItemAdded` or `ItemRemoved`. Now suppose this message is not a duplicated but a result of failure of previous send attempt and that the previous (successful) execution of business logic resulted in no state change. In that case obviously we should not re-publish an event in the next attempt at that message as there was nothing to be publishing in the first attempt.

Our code is obviously wrong. How can we fix it?

### Generating messages vs deriving messages

In the first attempt we are *generating* messages as we go in the process of executing the business logic. That ensures that the messages that are going to be sent out are in sync with the changes that are going to be applied to the database. In the second attempt when the changes in the database are already applied we are *deriving* the messages to be sent. What are we deriving them from?

### Deriving from incoming messages

In our case it is clear that we are deriving the outgoing messages from the incoming message. Got a `AddItem` message? Then clearly we need to re-publish an `ItemAdded` event with corresponding properties. As we've seen, that's not a good strategy for deriving messages.

### Deriving from the current state of the data

If not from the incoming message then maybe from the data stored? Unfortunately that would not work either as we don't know if the state has been modified in the first attempt at processing the current message or before.

### Deriving from the snapshot of state

If not from the incoming message and not from the current state then how? Well, the only correct way would be to derive the messages to be sent of from the snapshot of the state at the point when the initial attempt at sending messages was done. In order to do so the business logic would have to be able to access the state of the data at the point when message has been marked as processed. That approach can be achieved in two ways.

### Event sourcing

In event sourcing the state of an entity is not updated in place but rather represented as an ordered stream of events, each representing a single state change. The snapshot of the current state, when needed, is computed by application of a special state function on all events in order. Additional consequence of this approach is the fact that it is possible to compute the state as it was previously at any point in time.

### Storing multiple versions of the state

An alternative approach is to store a new snapshot of the state each time the state is modified. This way we can retried historical snapshots when needed.

### Complexity

Both described approaches are associated with significant additional complexity compared to the standard approach. Are we really doomed to adopt on of them in order to make our message derivation code correct? As you may suspect the answer is yes and no. Yes, if we want to continue depending on deriving messages then we need to adopt a storage approach that allows reconstructing state as it was at any moment in time. And no, we don't need it because message derivation is not the only solution. 

### Deterministic message dispatch

Let's take a closer look at what we really do need. When looking at a component from outside we need to ensure that message dispatch is deterministic i.e. that if we re-attempt to process the same message, the outgoing messages that are generated are exactly the same in both attempts.

We can achieve it by deriving the outgoing messages from the state of the data but that's not the only option. The alternative is to make the messages part of the state change itself. Remember the message processing transaction from the previous lecture:

```
begin tran

-- execute SQL statements resulting from the business logic execution
insert into ProcessedMessages (ID) values (`abc1234`)
commit tran
```

What if we extended in such a way that the `ProcessedMessages` also contains the serialized form of the messages that are going to be sent out?

```
begin tran

-- execute SQL statements resulting from the business logic execution
insert into ProcessedMessages (ID, OutgoingMessages) values (`abc1234`, `01101000101...`)
commit tran
```

Such a change allows us to simplify greatly the message processing logic. We no longer need to handle two cases in each message handler. All we need it to apply the business logic and prepare any messages that are going to be sent out. A piece of infrastructure (that can be shared between the handlers) will take these prepared messages, serialized them and store (as part of the same transaction).

Here's the pseudo-code that describes the behavior of an endpoint

```
BeginTransaction()
if (CheckIfMessageHasBeenProcessed) { //select exists from ProcessedMessages
    outgoingMessages = LoadOutgoingMessagesFromDatabase() //select from ProcessedMessages
} else {
    outgoingMessages = ExecuteBussinesLogic() //inserts and updates to business data
    MarkAsProcessed(messageId, outgoingMessages) //insert into ProcessedMessages
}
CommitTransaction()
Publish(outgoingMessages)
```

