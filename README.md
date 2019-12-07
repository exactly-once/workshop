# Consistent messaging in the cloud: how to build fault-tolerant distributed systems when throwing away consistency is not an option

## Elevator pitch

Building fault-tolerant distributed systems that maintain full consistency is not an easy thing. What makes it even harder is a lack of solid infrastructure foundations like distributed transactions. Forget about them. Learn to build reliable systems from the unreliable components available in the cloud.

## Description

This workshop focuses on building line-of-business, fault-tolerant, cloud-based distributed systems. These systems cannot afford to lose messages. Nobody wants their Christmas gift order to be lost. Neither can they duplicate messages. "There's a second Porsche in the driveway. Who ordered that?" In the past, these systems were built on the firm ground established by distributed transactions or large database instances that doubled up as message brokers.

These technologies are either too expensive, too cumbersome, or simply not available in the cloud. In this workshop, we will show you how to deal with the consistent messaging problem by duplicating and de-duplicating messages.

We'll start by asking ourselves the question of why the systems we build need to be distributed. We'll see how duplicating messages is the only way to get components to reliably exchange information. We'll spend most of our time identifying subtle issues inherent to message processing, devising solutions to these issues, and encoding these solutions in reusable patterns.

Join us for a series of ten hands-on exercises, interleaved with short lectures, after which you'll have a good understanding of most of the things that can go wrong when processing messages. You'll have enough knowledge to either build a bullet-and-duplicate-proof message processor or better, to identify a platform that does it for you.

## What will I learn?

For starters, you'll learn some solid reasons why distributed systems can offer significant advantages over monolithic systems. After we determine that distributing components of a system makes sense, we'll focus on the communication between these components. You'll learn why message de-duplication is a key part of a successful communication strategy.

Next, you'll learn the basic concepts of chaos engineering and how to use it in practice. You'll see how a messaging framework may be extended to simulate various types of failures that happen in real distributed systems. You'll use chaos engineering techniques to find flaws in a system even before it goes live.

You'll also experience how out-of-order message delivery can wreak havoc in message de-duplication strategies that seem otherwise perfect. Last but not least, you'll learn how to build a practical message de-duplication solution for your distributed system.

## Agenda

- Distributed asynchronous systems: why bother?
- Idempotent business logic
- Chaos engineering
- Simulating failures in a running system
- Messages are always delivered in order, aren't they?
- Simulating out-of-order delivery
- Message identity and identity-based de-duplication
- Outbox

## Structure

The workshop consists of interleaved lectures and practical exercises. The purpose of the exercises is for you to experience the problems first hand. The lectures are there to give you the contextual information and explanation. The exercises are designed to be chained together as each exercise builds upon the the previous one. They are difficult and that's by design. It's not a simple copy-paste thing. The goal is for you to struggle with them at least a little bit. But don't worry if you get lost midway. Each exercise has a pre-prepared starting point, so if you get stuck in one exercise, you'll still be able to start working on the next one.

## Prerequisites

The workshop exercises are built in C#/.NET. We won't use advanced features of the language/platform so don't worry if you don't have C#/.NET background. The exercise starting points already contain references to all required libraries (NuGet packages) and, whenever possible, we'll stick to basic C# constructs.

Below is the list of required software. All three apps are free or have free versions.

- [SQL Server Management Studio](https://docs.microsoft.com/en-us/sql/ssms/download-sql-server-management-studio-ssms?view=sql-server-2017)
- [SQL Server Express](https://www.microsoft.com/en-us/sql-server/sql-server-editions-express)
- [Visual Studio 2019](https://visualstudio.microsoft.com/pl/downloads/)

## About me

My name is Szymon Pobiega. I spent almost a decade working on various line-of-business software systems. Of all the ideas and patterns I learnt along the way, messaging had the biggest impact. I designed my first microservice system with MSMQ and NServiceBus 1.9 around ten years ago, and it was a life-changing experience.

Five years ago I quit consulting and joined Particular Software to use my experience in the field to make NServiceBus even better. I'm focused, in Particular (pun intended), on message routing patterns and handling of failures. 

During the last five years I've spent a great deal of time helping developers with issues related to communication in distributed systems. This workshop is based on real-world problems that people have struggled with.

Besides that, in my free time, I enjoy building remotely controlled vehicles with Lego.

## Lecture: Message delivery patterns in asynchronous systems

## Interlude: The system story and design

## Exercise 1: Idempotent business logic

## Lecture: Chaos engineering

- Chaos monkey
- Simulating message duplication
- Simulating broker failures

## Exercise 2: Simulate message duplication

## Exercise 3: Simulate database problems

## Exercise 4: Simulate broker problems

## Lecture: Coordinating data persistence and message publishing

## Lecture: Messages are delivered in-order

## Exercise 5: Allow removal of items

## Exercise 6: Bring in more chaos

## Lecture: Message IDs

## Exercise 7: ID-based de-duplication

## Exercise 8: Deterministic IDs

## Exercise 9: Even more chaos

## Lecture: Outbox

## Exercise 10: Outbox
