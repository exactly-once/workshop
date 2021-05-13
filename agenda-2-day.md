### Prerequisites
   * VS 2019 and .net472
   * Visual Studio Code and TLA+ extension
   * NServiceBus 7
   * CosmosDB Emulator

### Agenda

* Day 1
  - Block 1
    - [Introduction](https://exactly-once.github.io/workshop/Lectures/Intro.html)   
    - [Why distributed and asynchronous](https://exactly-once.github.io/workshop/Lectures/Why%20distributed%20and%20asynchronous.html) [script](https://github.com/exactly-once/workshop/blob/master/Lectures/Why%20distributed%20and%20asynchronous.md)
    - Intro to the project with [Exercise 1](https://github.com/exactly-once/workshop/tree/master/Exercise-1)
    - _Break_
  - Block 2
    - [Sources of duplication](https://exactly-once.github.io/workshop/Lectures/Sources%20of%20duplication.html#/5) [script](https://github.com/exactly-once/workshop/blob/master/Lectures/Sources%20of%20duplication.md)
    - Receiver-side duplication - [Exercise 2](https://github.com/exactly-once/workshop/tree/master/Exercise-2)
    - Sender-side duplication - [Exercise 3](https://github.com/exactly-once/workshop/tree/master/Exercise-3)
    - Simulated duplication - [Exercise 4](https://github.com/exactly-once/workshop/tree/master/Exercise-4)
    - _Break_
  - Block 3
    - DB failure simulation - [Exercise 5](https://github.com/exactly-once/workshop/tree/master/Exercise-5)
    - Broker failure simulation - [Exercise 6](https://github.com/exactly-once/workshop/tree/master/Exercise-6)
    - [Partial failures](https://exactly-once.github.io/workshop/Lectures/Partial%20failures.html) [script](https://github.com/exactly-once/workshop/blob/master/Lectures/Partial%20failures.md)
    - Follow-up to [Exercise 6](https://github.com/exactly-once/workshop/blob/master/Exercise-6/follow-up.md)
    - _Lunch Break_
  - Block 4
    - [Messages are delivered in-order](https://exactly-once.github.io/workshop/Lectures/Messages%20are%20delivered%20in-order.html) [script](https://github.com/exactly-once/workshop/blob/master/Lectures/Messages%20are%20delivered%20in-order.md)
    - Out of order - [Exercise 7](https://github.com/exactly-once/workshop/tree/master/Exercise-7)
    - [Message ID](https://exactly-once.github.io/workshop/Lectures/Message%20ID.html) [script](https://github.com/exactly-once/workshop/blob/master/Lectures/Message%20ID.md)
    - Id-based deduplication - [Exercise 8](https://github.com/exactly-once/workshop/tree/master/Exercise-8)
    - _Break_
  - Block 5
    - Follow up - Ex 8 - [Exercise 8](https://github.com/exactly-once/workshop/tree/master/Exercise-8)
    - Deterministic ID - [Exercise 9](https://github.com/exactly-once/workshop/tree/master/Exercise-9)
    - Non-deterministic messages - [Exercise 10](https://github.com/exactly-once/workshop/tree/master/Exercise-10)
    - [Outbox](https://exactly-once.github.io/workshop/Lectures/Outbox.html)

* Day 2 
  - Block 1 
    - Deterministic message generation - [Exercise 11](https://github.com/exactly-once/workshop/tree/master/Exercise-11)
    - [Integration testing messaging systems](https://github.com/exactly-once/workshop/blob/master/Lectures/integration-testing.pptx)
    - Predictable integration tests - [Exercise](https://github.com/exactly-once/workshop/tree/master/testing/Messaging.IntegrationTests)
  - Block 2
    - [Introduction to model-checking with TLA+](https://github.com/exactly-once/workshop/blob/master/Lectures/tla.pptx)
    - Model-checking outbox - [Exercise](https://github.com/exactly-once/workshop/tree/master/model-checking)
  - Block 3
    - Generic Outbox - [Exercise 12](https://github.com/exactly-once/workshop/tree/master/Exercise-12)
    - Inbox - [Exercise 13](https://github.com/exactly-once/workshop/tree/master/Exercise-13)
    - [Sync-async boundary](https://exactly-once.github.io/workshop/Lectures/Sync-Async.html)
  - Block 4
    - Token-based deduplication - [Exercise 14](https://github.com/exactly-once/workshop/tree/master/Exercise-14)
    - Out of document Outbox. Part 1 - [Exercise 15](https://github.com/exactly-once/workshop/tree/master/Exercise-15)
    - Out of document Outbox. Part 2 - [Exercise 16](https://github.com/exactly-once/workshop/tree/master/Exercise-16)
  - Block 5
    - [NoSql Storages - CosmosDB](https://github.com/exactly-once/workshop/blob/master/Lectures/cosmosdb.pptx)
    - [Http on the boundaries](https://github.com/exactly-once/workshop/blob/master/Lectures/azure-functions-http-boundaries.pptx)
    - [Azure Functions and CosmosDB case study](https://github.com/exactly-once/workshop/tree/master/Exercise-17)
