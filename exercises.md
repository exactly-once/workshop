## Exercise 1: Idempotent business logic

Questions:
- How can we ensure our duplicate handling works correctly?
- What should we do first, persist or publish?

## Exercise 2: Simulate message duplication

Questions:
- Do you see duplicates detected?
- There are messages indicating errors in processing that we have not seen in Exercise 1. Why?
- These error messages are logged at `INFO` level by the framework (NServiceBus). Why?

Follow up:
- Modify the duplicating behavior to duplicate only `AddItem` messages that are of type `Meat`.
  - Use `context.Message.Instance` in the `Invoke` method to get access to the outgoing message payload
  - Remember to check the type before trying to cast the payload object to specific type

## Exercise 3: Simulate database problems

Questions:
- Has `Billing` receive the `ItemAdded` notification?
- Has the state in the `Orders` endpoint changed?
- Is state of the system consistent?

Conclusion: Must not leak not state changes that have not been made persistent

## Exercise 4: Simulate broker problems

Questions:
- Have all events arrived at the `Billing` endpoint? Why?
- How can we solve it?

Conclusion: Must re-public messages if publishing failed

## Exercise 5: Allow removal of items

## Exercise 6: Bring in more chaos

Questions:
- What is the state of the system? What did you expect it to be?
- Why is the state inconsistent?
- How can we fix it?

Conclusion: The idempotence of each operation by itself is not enough if operations can be interleaved

## Exercise 7: ID-based de-duplication

Questions:
- Did it work?
- Why do we need to use the same `DbContext` in the de-duplication behavior and the handler?
- Why did the downstream endpoint receive a duplicate message?
- Can the downstream endpoint de-duplicate? How?

Conclusion: We need outgoing message ID generation logic to be deterministic

## Exercise 8: Deterministic IDs

Questions:
- Why do we need the name of the processing endpoint?

## Exercise 9: Even more chaos

Questions:
- Was the event published?
- What is the problem?

Conclusion: The logic for generating outgoing messages needs to be based on the version of the state that was current at the time the message has initially been processed, not on the incoming message

Conclusion 2: It is damn hard to achieve

## Exercise: Outbox

Questions:
- How do we make sure that if we fail after the first `SaveChanges` but before dispatching the dispatching is re-tried until succeeds?
- Can we use a different DB context in the de-duplicating behavior and in the handler?