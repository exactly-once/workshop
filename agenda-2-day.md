### Prerequisites
   * VS 2020 and .net472
   * Visual Studio Code and TLA+ extension
   * NServiceBus 7
   * CosmosDB Emulator

### Agenda

* Day 1
   - Introduction
     - lunch break   
   - (S) "Why distributed and asynchronous"
   - (S) "Definitions"
   - (S) Ex 1
   - _Break_
   - (T) "Sources of duplication" (includes ex 2 and 3)
   - (T) Ex 4 - simulated duplication
   - _Break_
   - (S) Ex 5 - db failure
   - (S) Ex 6 - broker failure - run
   - (S) "Partial failures"
   - (S) Ex 6 - follow up (fix code)
   - _Break_ (lunch break)
   - (T) "Messages are delivered in-order"
   - (T) Ex 7 - out of order
   - (T) "Message ID"
   - (T) Ex 8 - implement id-based deduplication
   - _Break_
   - Ex 8 - follow up (downstream)
   - Ex 9 - deterministic ID
   - Ex 10 - deterministic messages

* Day 2 
   - (T) CosmosDB
   - (T) Acceptance testing (slides + ex)
   - _break_
   - (T) TLA+ (slides + ex)
   - _break_
   - (T) External outbox in Cosmos DB with Azure Functions
   - Sync-async boundary
   
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
