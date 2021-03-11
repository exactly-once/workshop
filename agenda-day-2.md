# Agenda of day 2 of the 2-day workshop

Day to is focused on exploring various ways of implementing consistent messaging

### Lecture block

- Consistent messaging recap
- Message-Driven State Machines (MDSM)
- Event Sourcing

### Exercise

Build an event-sourced version of the add item command handler
 - Make Order a MDSM
 - Use provided event store

### Exercise

- Add `FirstItemAdded` event published when the first item is added to an order
- Test the handler with 'delayed failure when acking message` chaos monkey by adding two items quickly

### Brain storming

How can we ensure that messages are published exactly as when the message has been processed for the first time?

### Exercise

- Modify the logic of reconstructing the aggregate to return the state when the message was first processed
- Test the handler with 'delayed failure when acking message` chaos monkey by adding two items quickly

### Lecture block

- Discuss pros & cons of event sourcing-based approach
  - Snapshots
  - Evolving the code
- Outbox pattern

### Exercise

Build an Outbox-based version of the add item command handler
 - Make Order a MDSM
 - Use provided blob-based document store
 - Test the handler with 'delayed failure when acking message` chaos monkey by adding two items quickly
 
### Lecture block

- Discuss pros & cons of the outbox-based approach
  - Aggregate size becomes a problem. The more messages we process, the heavier it becomes

### Brain storming

What can we do to move the information about processed messages out of the aggregate?

### Exercise

Extract the Outbox logic out of the `AddItemHandler` to a separate `StateMachineRunner` class

### Exercise

Modify the `StateMachineRunner` to use the idea of the inbox

### Lecture block

- Consistency guarantees 101
- AWS S3 get-put-get flow is broken

### Brain storming

How can we modify the inbox flow to account for the broken get-put-get flow?

### Exercise

Modify the `StateMachineRunner` to cater for low-consistency stores such as S3

### Brain storming

How can we modify the inbox flow to move the information about processed messages out of the state machine data?

### Exercise

Modify the `StateMachineRunner` to use separate document for the outbox store to cater for storages that constraint the document size (400 KB in DynamoDB)

### Brain storming

What eviction policy can we use for the inbox? How long should we keep the de-duplication information in the inbox

### Lecture block

Deteministic de-duplication data evition via token-based protocol

### Exercise

Modify the `StateMachineRunner` to use token based protocol

### Lecture block

Summary

### Brain storming

Retrospective
