## Abstract

The goal of this workshop is to develop and test an infrastructure for end-to-end reliable communication in a distributed system that spans many different communication technologies.

The workshop focuses on building line-of-business, fault-tolerant, cloud-based distributed systems. Such systems cannot afford to lose messages (nobody wants their order for Christmas gifts to be lost) nor to get them duplicated (that second Porsche in the driveway -- who ordered that?). In the past, we used to build such systems on top of huge monolithic databases or on the firm ground of distributed transactions. These times have come to an end as these technologies are either too expensive, too cumbersome, or simply not available anymore.

Instead, we have other technologies in our toolbox: HTTP-based APIs, message queues, blob stores and super-scalable key-value stores. Neither of them offers similar guarantees to the technologies in the past but that's fine. In the course of this workshop we will combine these new tools to develop and test an infrastructure for end-to-end reliable communication in a distributed system that spans many different communication technologies.

## Agenda

The workshop consists of a set of hands-on exercises with short lectures in between. Each exercise takes 10-15 minutes to complete and is designed to move us one step closer to designing a reliable distributed system. Each exercise is split into two parts. In the first part, each attendee is given time to work on the problem independently. In the second part, all attendees attempt to solve it using the mob programming approach.

First, we'll explore the frontend of the system where the user interaction happens. We'll discuss the patterns for ensuring that the user's intent is captured in the most reliable way. In this module we'll focus in the transition between HTTP-based APIs and message-based asynchronous flows.

Next, we gonna look at the correctness requirements for an asynchronous message-driven distributed system. What guarantees are necessary for it to be able to execute the business process reliably? We will focus on the following aspects:

- how not to lose messages?
- how to prevent processing a single message multiple times?
- how to prevent propagating invalid state?

We will quickly survey various existing deduplication techniques, including embracing natural idempotency of data structures, immutable data structures, and identity-based deduplication.

In the third part we will attempt to design a deduplication algorithm from scratch and explore its various properties via prototyping and model-checking using the TLA+ toolset. Finally we'll put together a mimimum working implementation of the algorithm.

The fourth part will take us to the backend of the distributed system where our code often has to interact with APIs exposed by other systems or even third parties. In this section we are going to adapt the algorithm designed previously to the specifics of HTTP-based communication.

In the fifth part we will focus on the topic of large payloads. We will modify our code to cater for large message sizes and will exlore the concept of side effects of message processing looking for solutions to reliably storing large binary or text objects.

Finally in the sixth part, we will pull the camera back to see the entire system as it operates. In this section we are going to explore system-wide trends and patterns.

## Expected outcome

After the workshop you will understand the reasons for building distributed systems as opposed to centralized ones. You will be able to better articulate the need for going distributed and you will also know when to keep the good old monolith.

You will have hands-on experience designing and implementing a state-of-the-art distributed communication framework.

You will be able analyze and compare distributed algorithms shipped with third party software you use, design new ones, test their correctness and finally implement them in your systems. You will be able to make informed decisions when to use an off-the-shelf implementation build into a messaging framework of your choice and when to build one tailor-made for your problem.

You will understand when to use synchronous HTTP-based APIs and when to employ asynchronous messaging in order to maximize the desired qualities of your system while ensuring correctness of business processes flow that spans both communication technologies.


