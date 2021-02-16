### Prerequisites
   * VS 2020 and .net472
   * Visual Studio Code and TLA+ extension
   * NServiceBus 7
   * CosmosDB Emulator

### Agenda

* Day 1
   - "Why distributed and asynchronous"
   - "Definitions"
   - Ex 1
   - "Sources of duplication" (includes ex 2 and 3)
   - Ex 4 - simulated duplication
   - Ex 5 - db failure
   - Ex 6 - broker failure - run
   - "Partial failures"
   - Ex 6 - follow up (fix code)
   - "Messages are delivered in-order"
   - Ex 7 - out of order
   - "Message ID"
   - Ex 8 - implement id-based deduplication
   - Ex 8 - follow up (downstream)
   - Ex 9 - deterministic ID
   - Ex 10 - deterministic messages
   - "Outbox" (TODO: add publishing logic in the code snippet)
   - Ex 11 - implement outbox
* Day 2
   - Acceptance testing (TODO: slides)
   - TLA+ (TODO: slides, check order of labels, CosmosDB characteristics)
   - Ex 12 - Make outbox generic
   - Ex 13 - Introduce inbox
   - L8 - sync-async boundary
   - Ex 14 - Switch to token store
     - Switch to sync-async boundary
     - Switch from inbox checks to token store checks
     - Add section for creating tokens for outgoing messages
   - Ex 15 - Externalize outbox part 1 - transaction ID dictionary
   - Ex 16 - Externalize outbox part 2 - single transaction ID
   - Ex 16 - External outbox in Cosmos DB
     - implement store
   - Ex 17 - External outbox in Cosmos DB with Azure Functions
     - side-effects
     - http boundary
 
