### Prerequisites
   * VS 2019 or later
   * netcoreapp3.1
   * CosmosDB Emulator
   * Visual Studio Code and TLA+ extension

### Agenda

* Day 1
  - Block 1
    - [Introduction](https://exactly-once.github.io/workshop/Lectures/Intro.html)   
    - Intro to Cosmos DB
    - [Exercise 1 - A simple web application](Exercise-1/README.md)
  - Block 2
    - [Exercise 2 - State-based deduplication](Exercise-2/README.md)
    - [Exercise 3 - Optimistic concurrency](Exercise-3/README.md)
    - [Why distributed and asynchronous](https://exactly-once.github.io/workshop/Lectures/Why%20distributed%20and%20asynchronous.html) [script](https://github.com/exactly-once/workshop/blob/master/Lectures/Why%20distributed%20and%20asynchronous.md)
    - _Coffee break_
  - Block 3
    - [Exercise 4 - Make it asynchronous](Exercise-4/README.md)
    - [Sync-Async boundary](https://exactly-once.github.io/workshop/Lectures/Sync-Async.html)
    - [Exercise 5 - Monkeys of Chaos](Exercise-5/README.md) 
    - _Coffee break_
  - Block 4
    - [Exercise 6 - The USB Rule](Exercise-6/README.md)
    - [Partial failures](https://exactly-once.github.io/workshop/Lectures/Partial%20failures.html) [script](https://github.com/exactly-once/workshop/blob/master/Lectures/Partial%20failures.md)
    - [Exercise 7 - If in doubt, try again](Exercise-7/README.md)
    - [Sources of duplication](https://exactly-once.github.io/workshop/Lectures/Sources%20of%20duplication.html) [script](https://github.com/exactly-once/workshop/blob/master/Lectures/Sources%20of%20duplication.md)
    - [Exercise 8 - Automate it](Exercise-8/README.md)
    - _Coffee break_
  - Block 5
    - [Exercise 9 - Message duplication on the receiver side](Exercise-9/README.md)
    - [Primary-key based deduplication](https://exactly-once.github.io/workshop/Lectures/PK%20based%20deduplication.html)
    - [Exercise 10 - Primary key-based deduplication](Exercise-10/README.md)
    - Q & A
* Day 2
  - Block 1
    - [Integration tests](https://github.com/exactly-once/workshop/blob/master/Lectures/integration-testing.pptx)
    - [Exercise 11](Exercise-11/README.md) - Conversation-based integration tests
    - [Messages are delivered in-order](https://exactly-once.github.io/workshop/Lectures/Messages%20are%20delivered%20in-order.html) [script](https://github.com/exactly-once/workshop/blob/master/Lectures/Messages%20are%20delivered%20in-order.md)
  - Block 2
    - [Message ID](https://exactly-once.github.io/workshop/Lectures/Message%20ID.html) [script](https://github.com/exactly-once/workshop/blob/master/Lectures/Message%20ID.md) 
    - [Exercise 12 - Id-based deduplication](Exercise-12/README.md)
    - [Exercise 13 - Deterministic identifers](Exercise-13/README.md)
    - [Exercise 14 - State based message generation](Exercise-14/README.md) 
    - _Coffee break_
  - Block 3
    - [TLA+ - Intro](https://github.com/exactly-once/workshop/blob/master/Lectures/TLA%5EM%20in%20model-checking%20w%20praktyce.pptx)
  - Block 4
    - [TLA+ - Coding](https://github.com/exactly-once/workshop/tree/master/model-checking)
  - Block 5
    - [Outbox](https://exactly-once.github.io/workshop/Lectures/Outbox.html) [script](https://github.com/exactly-once/workshop/blob/master/Lectures/Outbox.md)
    - [Exercise 15 - Generic outbox](Exercise-15/README.md)
    - [Inbox](https://exactly-once.github.io/workshop/Lectures/Inbox.html#/)
    - [Exercise 16 - Generic outbox 2](Exercise-16/README.md)
    - [Exercise 17 - Generic outbox 3](Exercise-17/README.md)
    - [Exercise 18 - Outbox with inbox](Exercise-16/README.md)
    - _Coffee break_
  - Block 6
    - [Deduplication types](https://exactly-once.github.io/workshop/Lectures/Deduplication%20types.html)
    - [Azure Functions Case-Study - Exercise](https://github.com/exactly-once/workshop/tree/master/azure-functions-cs)       
    - Q & A
