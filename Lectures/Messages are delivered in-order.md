# Messages are delivered in-order

Bare with me for a couple more minutes until we again dive deep into the code. I'd like to take briefly about message ordering. Who thinks message queues guarantee message order? Well they are pretty good in maintaining the order but unfortunately there are cases where messages sent between two endpoints get re-ordered.

## Clustering

Some message infrastructures enforce that a single queue is hosted on a single node of the cluster. This allows them to ensure that, given that node is up and running, the order of messages is preserved. Unfortunately this approach has two downsides. First, when the node is down then all the queues it hosted are unavailable. Second, the queue can only hold as many messages as the node can fit. In other words, a queue cannot outgrow the machine it is hosted at.

There are some infrastructures that try to solve the fist problem by introducing primary-secondary approach where each given queue has a backup (secondary) node that takes over when the primary is down. Although it sounds good, in practice the problem is reliable failure detection. What it the network between the secondary and primary replica is faulty? Both think the other is down so both try to accept and serve messages. Clients might end up using both replicas at the same time. When the connection is back again which replica should be treated as a source of truth? This problem can be mitigated by using quorum-based consensus where each operation (send or receive) has to be accepted by a quorum of nodes.

Other infrastructures try to solve the second problem assuming that if a queue is partitioned between multiple nodes and one of the nodes is down, the application that uses it won't even notice. The simplest scheme is round-robin where messages are distributed between a set of nodes. If one the nodes goes down for a while, the receiver won't get messages from it. Instead, these messages will be served when that nodes comes up again. The initial order of messages is lost now.

## Concurrent processing

For throughput reasons in all practical applications the message processing is concurrent. Regardless if that concurrency is achieved by running multiple threads or by using a single event loop, the result is that multiple messages are being processed at any given point in time. The rationale for this approach is the fact that message processing is rarely CPU-bound. Most likely a message handler is going to interact with components that are IO-bound, such as file systems or databases. Any modern hardware can handle multiple concurrent IO-bound operations so restricting the message processing to a single message at a time would be a huge waste of processing power.

Imagine messages `a` and `b` neatly ordered one after the other `ab` in the queue. Thread `A` receiver message `a` from the head of the queue and a millisecond later thread `B` receives message `b`. Immediately thread `A` executing ist handler logic hits a database and pauses as the DB server detects that a lock is held on a row that `A` wants to access. Fortunately for `B`, the data it needs is not locked so `B` proceeds and completes processing of `b`. After a while the data that `A` needs is unlocked and it can continue its work. The result is that the data modifications resulting from processing messages are applied in the reverse order, first `b` and then `a`.

## Failure handling

Messaging endpoints deal with transient problems by backing off and re-trying processing. If an exception is thrown while handling a given message, the message receive transaction is rolled back and the message gets back into the queue. If the nature of the problem is indeed transient, the processing is going to succeed in the next attempt or the following attempt. Otherwise, after a certain number of attempts the message is moved to a *poison queue* where it awaits manual handling. Maybe that message was malformed? Or maybe it has been misrouted? 

When the issue with that message is fixed, it is sent back to its destination queue but at that time, some messages that were sent after it might have already been processed. The order that sender tried to enforce is lost.

## Alternatives

Messages arriving out-of-order is a fact of life and you need to be prepared to deal with it. Or maybe not? Are there any alternatives?

## Log

In the recent years logs, and especially distributed replicated logs, became very popular. One of the differences between a traditional messaging infrastructure and a log is the fact that in a log the order of entries is stable. Once an entry is added to a log, it is assigned a position (or index) and it is going to retain the same position forever (or until the log is truncated). So do logs solve the problem of out-of-order messages? Not really.

First, logs are usually not monolithic. They contain separate independent *streams* and usually (EventStore is a notable exception here) there is no total order between *streams*. Second, *streams* are divided into partitions so there might not be a total order even within a single *stream* (depending on technology). 

Where the logs have advantage over queues is the receiver side. Because logs don't push items at the consumer but rather allow consumers to consume at their own pace and using their own algorithms, the receiver can be built in such a way that it consumes log entries in order. Such a consumer would have to be single-threaded and use a blocking failure handling strategy. It means that whenever consuming a log entry results in a non-transient issue, the consumer would have to be blocked until the issue is resolved, likely by manual intervention. Such a strategy makes sense in certain specific cases.

## Total order

Let me get back for a moment to the idea of total order of entries. As I mentioned, there are some technologies like Event Store or Aeron that are capable of handling large logs while maintaining total order of entries. These systems were built with very high throughput and low latency in mind so they are probably offer good-enough performance for most standard business cases. Wouldn't it be great if we could replace our aging messaging infrastructure with a tool like one of these are never ever have to worry about the order of messages?

My point of view is that they live at a different level when it comes to the system's architecture. Using Event Store or Aeron requires that all the components of the system agree not only on the technology stack but also on the structure of the log. That's significant coupling, in my opinion comparable the database integration we talked before. It is OK to have groups of components that share the Event Store or Aeron log that would not be the components when you look at the architecture at the highest level.

I would argue that at the highest level the system consists of autonomous components that should share nothing (no database nor log) and communicate (sporadically) by passing messages via the dumbest type of durable messaging infrastructure available. The less a component assumes about the communication infrastructure the easier is to integrate with it. For me the defining property of such component is the fact tha it **defines its own order of events**. This means while there is no defined order between signals (coming from other components) that such component receives, there is a single defined order at which these signals have been processed and the results of the processing have been persisted.

Given messages `a`, `b` and `c` coming to our component via message queue roughly at the same time, the result might be that the database will have the operations persisted as `abc` or `bca` but once persisted, that order will never change. If the first persisted state is `a` and then `ac`, it is impossible that in some moment in future there will be state `ab` visible as `c` has been made persistent before `b`. If that component publishes events that inform others about its state transitions, there never can be an events that informs about state `ab` as it never existed.