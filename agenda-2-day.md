### Prerequisites
   * VS 2020 and .net472
   * Visual Studio Code and TLA+ extension
   * NServiceBus 7

### Agenda
* Day 1
  * 3.5h
    * P: Why do we need to distribute our code
    * P: Synchronous vs asynchronous communication.
    * Ex: Writing you first message handler (maybe creating pairs of participants)
    * Q: AhaSlides
    * P: How does message duplicates happen
    * Ex: Show duplicated behavior (maybe with a too short Time-to-Process)
  * 1h - lunch
  * 3.5h
    * P: Basic message deduplication techniques
        * Ex 3-8 from the 1-day worshop
    * 
* Day 2
  * Designing and testing distributed algorithms
    * How to write reliable att for message based systems
  * Intuition and heuristics for writing reliable message based systems
  * TLA+
    * Mob programming with testing some of ideas and running through failure stacks
  * Commertial tools
  * 1h - lunch
  * Advanced deduplication techniques for infinite-scale databases
    * Implement outbox store
    * Implement messaging system integration
    * Side-effects modelling
  * P: Deterministic (token-based) deduplication
  * P: HTTP communication/demo


TODO:
 * Go through ex and figure out how to add slides/quizes
 * TLA+ one of the algorithms from day 1 showing failing trace
 * Advanced deduplication techniques
