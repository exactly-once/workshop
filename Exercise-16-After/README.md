# Exercise 16: Out-of-document outbox - part 2

In the previous exercise we have limited the footprint of the outbox to a mere dictionary containing transactions that are currently in progress. 

In this exercise we will push this algorithm to its limit and leave only a single `string` field related to the deduplication.

To do this we need to realize that there is no value in having multiple in-progress transactions. They are not really in progress. Once the changes are committed, the in-progress transaction represents only the remaining work that needs to be completed, namely dispatching of the outgoing messages. 

How to ensure outgoing messages are pushed when dropping the transactions dictionary? 
