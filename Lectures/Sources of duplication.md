# Sources of duplication

Where do these duplicates come from? There are three main sources of duplicates. 

## Sender

First, the process of ensuring at-least-once delivery requires the sender to re-try sending a message until it gets a confirmation from the messaging infrastructure. Because the sending of a message is a remote call, the confirmation might not get delivered to the sender. In such case the sender has no way to know if the message has been sent so the only thing it can do is try again. If the first attempt succeeded then the second one introduced a duplicate.

## Middleman

Next, the message infrastructure can introduce duplicates when handling the message. It is rarely the case that the messaging infrastructure is a single process on a single machine. For performance and reliability reasons such infrastructures are often federated or replicated. Federated infrastructure consists of multiple nodes that forward messages between them. Each hop can introduce a duplicate in the same way as sender does. Replicated infrastructure uses multiple storage nodes to store messages of a single queue in case one of the nodes gets toasted. Network splits can lead to messages being delivered to the receiver from more than one node.

## Receiver

Last, but not least, the receiver can cause a single message to be processed more than once. Such situations happen when the receiver executes its processing logic but, for some reason, fails to acknowledge processing that message with the messaging infrastructure. Such message is re-delivered to the receiver.

# Exactly once

Now that we discussed at-most-once and at-least-once, let us circle back to the behavior we would actually **like** to have, the exactly-once delivery. Given that we know that duplicates are a fact of life and will get introduced every now and then, in order to achieve this we would have to build a messaging infrastructure that does de-duplication on behalf of the receiver.

## De-duplication

Given that messaging infrastructure and the receiver are two separate processes, we know what would be necessary here: distributed transactions. Unfortunately there is only one such product available and is now in life-support mode, MSMQ. Most message brokers do not support distributed transactions and are not going to do so in future due to reasons we discussed previously. What is the alternative? 

The alternative is to code the business logic of **A** and **B** in such a way that processing `a` and `b` multiple times results in `X` and `Y` being applied only once so that for an outside observer, the outcome of a single `a` message is the same as multiple `a` messages.
