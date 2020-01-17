# 120 minute version of the workshop

## Main limitations

- Based on an in-memory data store to make the setup easier
- Some exercises are skipped
- Some exercises are limited

## Agenda

- Introduce distributed business processes
- Introduce the story (pierogi)
- Ex 1
  - Based on an in-memory DB
  - Fill in the handler code
    - Load order
    - Add item
    - Publish event
    - Store order
- Introduce chaos engineering
- Ex 2 - Simulate duplicates
  - Add duplicate generation
  - Run the solution
  - Fix the problem by introducing a duplicate detection code based on the types of filling
- Ex 3 - Ghost messages
  - Add validation logic to OrderRepository
- Consistent messaging
- Ex 4 - Broker failure
- Ex 6 - out-of-order duplicates
- Message ordering
- Message ID
- Ex 7 - ID-based de-duplication
  - Make ID part of Item
  - Keep the de-duplication code in the handler
- Ex 8 - deterministic IDs
- Ex 9 - state-based publishing logic
  - Add the logic for publishing "Second item added" event
  - Add `Delay` to the broker failure behavior
- Discuss how to solve the problem
  - Restore previous state
  - Store outgoing messages
- Outbox pattern
  - Problems
- Sneak peek into further developments
  - Inbox
  - Claims
  - Circular buffer