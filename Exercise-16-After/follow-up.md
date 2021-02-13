# Exercise 16: Out-of-document outbox - part 2

If we replace the dictionary with a single field, we might end up in a situation where processing of message `n` failed before dispatching and before this message is retried, message `m` has been picked up. The processing code loads the entity and detects a non-null `TransactionId`. What should it do?

It needs to complete the work. Let's get to work. First, replace the dictionary with a single `TransactionId` field and fix the assignment and cleanup.

Next we need to add the code that finishes the processing. That code is going be run even before we check the inbox.
 - Check if `TransactionId` is not `null`
 - If so, load the outbox state
 - If it is not `null`
   - Dispatch the messages
   - Remove the outbox
   - Mark that message as processed
   - Clear the `TransactionId` and store the entity

Because the cleanup is now part of processing each message, we can safely remove the cleanup code from the case when inbox store contains the message.

Last but not least, the condition based on `TransactionIds`. We can remove that one too. The code we added at the top ensures that when we get to this point, the `TransactionId` is `null` and the message is not a duplicate.

Let's look at the code now. There is slight duplication there that we can remove. Extract `FinishTransaction` method.