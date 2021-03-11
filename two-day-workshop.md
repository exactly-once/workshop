Building reliable event-driven microservices architectures: making sure all messages are processed exactly once

### Abstract

The workshop focuses on building line-of-business, fault-tolerant, cloud-based distributed systems. Such systems cannot afford to lose messages (nobody wants their order for Christmas gifts to be lost) nor to get them duplicated (that second Porsche in the driveway -- who ordered that?). In the past, we used to build such systems on the firm ground established by distributed transactions or large database instances - serving both as business data stores and messaging brokers. These times have come to an end as these technologies are either too expensive, too cumbersome, or simply not available anymore.

Through the workshop, you will learn how to use simple and inexpensive components available in the cloud to build reliable and robust systems that don't compromise consistency. The key to this is making peace with message duplication (yes, that's a fact of life) and understanding how and where it can be dealt with.

Some of the topics we are going to cover:
 - Synchronous vs asynchronous communication in microservices
 - Message delivery guarantees and message deduplication
 - Designing and testing distributed algorithms
 - Working effectively with infinite-scale databases such as DynamoDB or Cosmos DB
 - Reliable and robust communication via HTTP

### Details

The workshop consists of ~15 hands-on exercises with short lectures in between. Each exercise takes 10-20 minutes to complete and is designed to move us one step closer to designing a reliable distributed system. Each exercise is split into two parts. In the first part, each attendee is given time to work on the problem independently. In the second part, all attendees attempt to solve it using the mob programming approach.

First, we will learn the advantages and pitfalls of synchronous and asynchronous architectures. In order to maximize the benefits of both approaches, we will split our system into two parts, the outer synchronous part, and the inner asynchronous core. Next, we will take a look at the very place where these two parts come together - a so called sync-async boundary.

Next, we gonna look at the correctness requirements for an asynchronous message-driven distributed system. What guarantees are necessary for our core async components to be able to execute the business process reliably? We will focus on the following aspects:
 - how to not lose messages?
 - how to prevent processing a single message multiple times?
 - how to prevent propagating invalid state? 

We will explore various deduplication techniques, including embracing natural idempotency of data structures, immutable data structures, and identity-based deduplication.

In the third part we will explore techniques for ensuring correctness of our code, specifically:
 - how do develop intuition for building distributed algorithms
 - how to test concurrent code with hundreds and thousands of possible execution paths
 - how to use model-checking tools such as TLA+

The four part will take us to the advanced deduplication techniques required for the modern infinite scale databases such as DynamoDB and Cosmos DB. In this part we will develop algorithms designed to work with constraints of such databases e.g. limited entity size and lack of cross-partition transactions.

In the next part we will re-examine the identity-based deduplication strategy with its advantages and pitfalls. We will attempt to develop an algorithm that removes some of the flaws of the classic identity-based approach.

Finally, in the sixth part we we will pull the camera back to see our distributed system in its context. We will examine how systems communicate and analyze the requirements for correct communication. Next, we will attempt to build a HTTP-based communication protocol that is compatible with the design decisions we have made so far in our attempt to build a robust event-driven system.

### Expected outcome

After the workshop you will understand the reasons for building distributed systems as opposed to centralized ones. You will be able to better articulate the need for going distributed and you will also know when to keep the good old monolith.

You will know the difference between a single-resource and a distributed transaction. You will also understand why cloud vendors are unlikely to ever provide a general-purpose distributed transaction support and why you need to use an alternative approach to maintaining consistency.

You will be able to partition your system into synchronous and asynchronous parts in order to provide best user experience while not compromising on reliability nor throughput.

You will be able analyze and compare distributed algorithms shipped with third party software you use, design new ones, test their correctness and finally implement them in your systems. You will be able to make informed decisions when to use an off-the-shelf implementation build into a messaging framework of your choice and when to build one tailor-made for your problem.

Finally you will know proven patterns for ensuring consistency in the asynchronous part of your system without the need for using distributed transactions.

### Agenda

#### Day 1

 - Why do we need to distribute our code
 - Synchronous vs asynchronous communication. 
 - Basic deduplication message deduplication techniques
 - Designing and testing distributed algorithms

#### Day 2

 - Advanced deduplication techniques for infinite-scale databases
 - Deterministic deduplication
 - Reliable and robust HTTP communication
