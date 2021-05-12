### Prerequisites
   * VS 2020 and .net472
   * Visual Studio Code and TLA+ extension
   * NServiceBus 7
   * CosmosDB Emulator

### Agenda

* Day 1
   - [Introduction](https://exactly-once.github.io/workshop/Lectures/Intro.html)   
   - [Why distributed and asynchronous](https://exactly-once.github.io/workshop/Lectures/Why%20distributed%20and%20asynchronous.html)
   - Intro to the project with [Exercise 1](https://github.com/exactly-once/workshop/tree/master/Exercise-1)
   - _Break_
   - [Sources of duplication](https://exactly-once.github.io/workshop/Lectures/Sources%20of%20duplication.html#/5) 
   - Receiver-side duplication - [Exercise 2](https://github.com/exactly-once/workshop/tree/master/Exercise-2)
   - Sender-side duplication - [Exercise 3](https://github.com/exactly-once/workshop/tree/master/Exercise-3)
   - Simulated duplication - [Exercise 4](https://github.com/exactly-once/workshop/tree/master/Exercise-4)
   - _Break_
   - DB failure simulation - [Exercise 5](https://github.com/exactly-once/workshop/tree/master/Exercise-5)
   - Broker failure simulation - [Exercise 6](https://github.com/exactly-once/workshop/tree/master/Exercise-6)
   - [Partial failures](https://exactly-once.github.io/workshop/Lectures/Partial%20failures.html)
   - Follow-up to [Exercise 6](https://github.com/exactly-once/workshop/blob/master/Exercise-6/follow-up.md)
   - _Lunch Break_
   - [Messages are delivered in-order](https://exactly-once.github.io/workshop/Lectures/Messages%20are%20delivered%20in-order.html)
   - Out of order - [Exercise 7](https://github.com/exactly-once/workshop/tree/master/Exercise-7)
   - [Message ID](https://github.com/exactly-once/workshop/blob/master/Lectures/Message%20ID.html)
   - Id-based deduplication - [Exercise 8](https://github.com/exactly-once/workshop/tree/master/Exercise-8)
   - _Break_
   - Follow up - Ex 8 - [Exercise 8](https://github.com/exactly-once/workshop/tree/master/Exercise-8)
   - Deterministic ID - [Exercise 9](https://github.com/exactly-once/workshop/tree/master/Exercise-9)
   - Deterministic messages - [Exercise 10](https://github.com/exactly-once/workshop/tree/master/Exercise-10)

* Day 2 
   - (T) CosmosDB
   - (T) Acceptance testing (slides + ex)
   - _break_
   - (T) TLA+ (slides + ex)
   - _break_
   - Outbox with Ex 11, ex 12
   - _break_
   - Ex 13, 15, 16
   - _break_
   - Sync-async boundary
   - External outbox in Cosmos DB with Azure Functions
    
   
 * Other
   - Ex 11 - implement outbox
   - (T) CosmosDB
   - _break_ 
   - (T) TLA+
   - Ex 12 - generic Outbox 
   - Ex 15, 16 - out of document Outbox 
   - _break_ (longer)
   - (T) Ex 12 - Make outbox generic
   - (T) Ex 13 - Introduce inbox
   - _break_ 
   - (S) L8 - sync-async boundary
   - (S) Ex 14 - Switch to token store
     - Switch to sync-async boundary
     - Switch from inbox checks to token store checks
     - Add section for creating tokens for outgoing messages
   - _break_
  
   - _break_
   - Ex 16 - External outbox in Cosmos DB
     - implement store
   - _break_ 
   - (T) Ex 17 - External outbox in Cosmos DB with Azure Functions
     - side-effects
     - http boundary
   - Q/A
