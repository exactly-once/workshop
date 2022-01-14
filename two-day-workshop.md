Building reliable event-driven microservices architectures: making sure all messages are processed exactly once

### Abstract

The workshop focuses on building line-of-business, fault-tolerant, cloud-based distributed systems. Such systems cannot afford to lose messages (nobody wants their order for Christmas gifts to be lost) nor to get them duplicated (that second Porsche in the driveway -- who ordered that?). In the past, we used to build such systems on top of huge monolithic databases or on the firm ground of distributed transactions. These times have come to an end as these technologies are either too expensive, too cumbersome, or simply not available anymore.

Instead, we have other technologies in our toolbox: HTTP-based APIs and message queues. Neither of them offers similar guarantees to the technologies in the past but we can learn how to combine them to create systems that behave correctly even in face of failures.

The workshop consists of ~15 hands-on exercises with short lectures in between. Each exercise takes 10 minutes to complete and is designed to move us one step closer to designing a reliable distributed system. Each exercise is split into two parts. In the first part, each attendee is given time to work on the problem independently. In the second part, all attendees attempt to solve it using the mob programming approach.

### Agenda

First, we'll explore the frontend of the system where the user interaction happens. We'll discuss the patterns for ensuring that the user's intent is captured in the most reliable way. In this module we'll focus in the transition between HTTP-based APIs and message-based asynchronous flows.

Next, we gonna look at the correctness requirements for an asynchronous message-driven distributed system. What guarantees are necessary for it to be able to execute the business process reliably? We will focus on the following aspects:

- how not to lose messages?
- how to prevent processing a single message multiple times?
- how to prevent propagating invalid state?

We will explore various deduplication techniques, including embracing natural idempotency of data structures, immutable data structures, and identity-based deduplication.

In the third part we will explore techniques for ensuring correctness of our code, specifically:

- how do develop intuition for building distributed algorithms
- how to test concurrent code with hundreds and thousands of possible execution paths
- how to use model-checking tools such as TLA+

The fourth part will take us to the backend of the distributed system where our code often has to interact with APIs exposed by other systems or even third parties. We will discuss patterns to ensure reliable communication with these external agents.

Finally in the fifth part, we will re-examine the most common, identity-based, deduplication strategy with its advantages and pitfalls. We will attempt to develop an algorithm that removes some of these flaws.

### Expected outcome

After the workshop you will understand the reasons for building distributed systems as opposed to centralized ones. You will be able to better articulate the need for going distributed and you will also know when to keep the good old monolith.

You will understand when to use synchronous HTTP-based APIs and when to employ asynchronous messaging in order to maximize the desired qualities of your system while ensuring correctness of business processes flow that spans both communication technologies.

You will know the difference between a single-resource and a distributed transaction. You will also understand why cloud vendors are unlikely to ever provide a general-purpose distributed transaction support and why you need to use an alternative approach to maintaining consistency.

You will be able analyze and compare distributed algorithms shipped with third party software you use, design new ones, test their correctness and finally implement them in your systems. You will be able to make informed decisions when to use an off-the-shelf implementation build into a messaging framework of your choice and when to build one tailor-made for your problem.
