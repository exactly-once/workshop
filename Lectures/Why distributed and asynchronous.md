# Message delivery patterns in asynchronous systems

## Why distributed?

First of all we should ask ourselves a question: why both with distributed asynchronous systems? Wouldn't it be better to just build synchronous non-distributed ones? It certainly would be easier.

### What is a distributed system?

A system is *distributed* if it consists of multiple components and these components are running inside different processes. The fact that these components are part of a single system means they need to communicate to realise functions of that systems. If there was no requirement for communication then we could call them separate non-distributed systems.

### Communication in a distributed system

Communication across process boundaries is much more difficult than within a single process. A call to another service needs to be converted into a message that can be transmitted over the wire. On the other side a similar mechanism needs to unpack the message and convert it back into a function call. There are many things that can go wrong in the meantime, including but not limited to network issues and process downtime.

### So, why distributed?

So why do we distribute components of our systems? The main reasons are following.

### Maintenance

Maintenance in software is a process by which an existing software system is extended with new functionality after being deployed to the production environment. Traditionally there were two separate and well-defined stages of software system: construction and maintenance. The assumption used to be that the majority of important features of the software system are delivered in the construction phase in which that system is not yet operational. At the end of the building phase the system is deployed to a production environment and the process transitions to the maintenance stage in which only minor features and bug-fixes are delivered periodically until the system can be finally decommissioned.

#### There is no construction, just maintenance

Today the transition between the phases is much more blurry and usually happens much earlier, even at the very beginning of the process. That means that major features are continued to be delivered while the system is operational. This change in the process influences how software systems are designed. Out of the necessity to deliver major features to a production system the idea of isolation was born. 

#### Isolation to the rescue

If we split the system into multiple processes it would be possible to stop, deploy and restart part of the system independently. Changes could be deployed and verified in production in a gradual fashion without the need of a Big Bang deployment of a whole system.

### Failure tolerance

#### Machine crash

When we think about failure in software system we usually picture machines being toasted. As a result the process that was running our components dies and all users who were connected to that process need to be migrated to a different one. This process is called fail-over and is well-known and well-understood by our industry. Non-distributed systems are generally good in handling this failure mode. 

#### Stateless

The long time best-practice was to keep the middle tier of a system stateless and keep all state in the database. The rationale here being that if you have no state, you can't lose it when your host becomes a pile of ash. If you followed that practice and one of your processes died, you could easily switch users to other processes that run exactly the same code/binaries.

#### Bugs

Unfortunately a machine crash is not the only failure mode. More dangerous failures are results of defects in the code. These defects might cause failures in a deterministic manner or be triggered by some external condition i.e. February 29th. Their evil-doing potential comes from the fact that running multiple copies of the process does not help as all the copies are going to be affected at the same time.

#### Starvation

Investigation of such failures reveals that they are often caused by a single malfunctioning component that, e.g. starts to consume all available memory, eventually causing whole process to crash. This leads to the idea that physically isolating components can prevent a failure in one to bring the whole system down. The system might suffer from reduced functionality for a while but at least it will be running.

### Scalability

For a long time scalability in software was dealt with in the same way as the failure tolerance i.e. by running multiple copies of the system. When the load increases more instances can be provisioned on demand. Unfortunately it only works well for the HTTP traffic. You can't scale the nightly batch process simply by running more instances of the process. By allowing components to run in different processes you can optimize scaling for the specific behavior of a given component.

### Data store

So far we talked about the middle tier which is focused on computing. Let's now take a look at the data tier. Should we distribute the data between multiple stores? 

#### Distributed or centralized?

Let's assume we have already decided to distribute our middle tier components. What would prevent us from having a separate data store for each of these components?

### Database integration

The answer is the dreadful database integration. As mentioned above, communication across the process boundary is difficult and prone to failures. 

#### Atomic transactions and process boundaries

Atomic transactions (with some notable but irrelevant exception) cannot span process boundaries. This means that a if component **A** wants to modify data `X` and call component **B** (in a different process) to modify data `Y`, they can't ensure both changes are done atomically. Database integration offers a simple solution to this problem. Just let component **A** modify both `X` and `Y` and component **B** poll database for changes in `Y`. This way Y will get reliably notified when `Y` changes.

#### The dark side of database integration

Unfortunately database integration has a dark side to it. When each and every component can modify any piece of the shared data store, none of these components can evolve independently of others. Very quickly the data store schema fossilizes. Nobody can remove a single column, ever. This is why we, as in industry, have learned to avoid database integration at all cost.

#### Distributed!

This leaves us with the only viable option to use separate data stores for each component. Depending on the requirements, these data stores might all be of the same type (e.g. SQL) or there might be specialized ones e.g. graph databases or time series databases.

## Why asynchronous?

So far we've dealt with the *why distributed* question. Let's now focus on the asynchronous part. Why asynchronous? 

### Atomic transactions and process boundaries, revisited

Recall the scenario we discussed a bit earlier when component **A** wanted to modify data `X` and call component **B** to modify data `Y`. We've seen that due to lack of shared transaction context we can't execute this scenario atomically i.e. ensuring that either both **X** and **Y** are modified of none is. So can we afford to give up atomicity? Many people will tell you that this is precisely what you need to do in the cloud. I call it BS. Cloud or not, we need to build systems that ensure consistent data modifications.

### Pixie dust

Can we then use some magic to create the shared transaction context between **A** and **B**? As it turns out we can. This technology is called distributed transactions and is quite old. So why not just use it and avoid asynchrony? There are two problems with this technology. First, it is not widely available. The lock-heavy nature of Two-Phase-Commit protocol used in distributed transactions is not well suited for shared cloud infrastructure which means that cloud-native data stores won't play ball with distributed transactions.

### Locks, locks everywhere

The second problem is also rooted in the lock-heavy nature of the distributed transactions. In order to guarantee that all involved parties can commit the transaction, locks need to be held by all participants for the whole duration of the transaction. This greatly limits the autonomy of components as one faulty component that is unable to commit its transactions can bring the whole system to a halt.

### Alternative

So what is the alternative? We can't really guarantee that `X` and `Y` are modified atomically but we can do guarantee something that is almost as good from business point of view. We can ensure that if `X` is modified then `Y` will be eventually modified too. 

### Eventual consistency

We can do this by introducing durable messaging infrastructure between **A** and **B**. With that infrastructure **A** can send a message to **B** and the messaging infrastructure will guarantee that the message will be eventually delivered. Let's assume that message `a` arrives at queue `Q_A`. The message is picked up by **A** and processed. As a result, message `b` is put into queue `Q_B` and `X` is modified. Later, **B** picks up a message from queue `Q_B` and, as a result, modifies `Y`. Any failure while processing a message causes that message to be returned to its queue (where it is durably stored). The outlined scheme provides the very guarantee we were seeking, namely that if `X` is modified then `Y` will be eventually modified as well. 

## Queue and Database

### Building blocks

So far we went through reasons for choosing distributed over co-located and asynchronous over synchronous. This choice leads us to a design where all complex processes are build from a single type of three-step activity:
- receive a message
- update a data store
- send messages
By chaining together such simple activities one can build processes of any length and complexity. There is one problem, though. Remember how we discussed that two processes can't share the same transactional context? 

### Back to square one?

Guess what, the business process and the message infrastructure are two separate processes. Without distributed transactions (and we already discussed why they aren't a good fit for most modern systems) one cannot guarantee that data will be modified atomically with sending a message. This leaves us with two options.

### At most once

The at-most-once behavior is a best-effort approach in which a message send attempt is done once in hope it succeeds. In case of failure the message there is no attempt to re-send that message. While this mode of operation is useful in some domains (imagine a stream of sensor readings; losing a message every now and then is not a problem), it is generally not acceptable in most cases. In out example of components **A** and **B**, if sending of message `b` to `Q_B` fails, the system will end up in an inconsistent state where `X` is changed by `Y` is not (and will never be).

### At least once

The opposite approach is called at-least-once. In this mode the sender is obliged to retry sending a message until it gets a confirmation from the messaging infrastructure that the message has been durably persisted. You can probably feel that there is a trade-off somewhere and you are right. The trade-off is that we need to be able to handle duplicates -- multiple copies of the same message. Looking again at our components **A** and **B**, in order to apply at-least-once strategy the logic in **A** and **B** would have to be written in such a way that processing messages `a` and `b` multiple times would result in `X` and `Y` being applied as if messages were processed once. As we will see during the course of these workshops, that is much easier said than done.
