# Consistent messaging in the cloud. How to build fault-tolerant distributed systems when throwing away consistency is not an option

The workshop focuses on building line-of-business fault-tolerant cloud-based distributed systems. Such systems cannot afford to lose messages (nobody wants their order for christmas gifts to be lost) nor to them (that second Porsche in the drive way -- who ordered that?). Such systems were, in the past, built based on the firm ground established by either distributed transactions or large database instances that served also as messaging brokers.

These technologies are either too expensive, too cumbersome or simply not available in the cloud. In this workshop we will show how one can deal with the consistent messaging problem by de-duplicating messages.

We'll start by asking ourselves a question why the systems we build need to be distributed. We'll see how duplicating messages is the only way to get components to reliably exchange information. Finally, we'll spend most of our time identifying subtle issues inherent to message processing, devising solutions to these issues and encoding these solutions in reusable patterns.

Join me in the series of ten hands-on exercises interleaved with short lectures after which you'll have good understanding of most of the things that can go wrong when processing messages and enough knowledge to either build build a bullet-and-duplicate-proof message processor or (even better) find a framework that implements one for you.

## What will I learn?

For start you will learn some solid reasons why distributed systems offer a significant advantage over monolithic ones. Once we all agree that distributing components of the system makes sense, we will focus on the communication between these components. You'll learn why message de-duplication is a key part of a successful communication strategy.

Next, you will learn the basic concepts of chaos engineering and how to use it in practice. You will see how a messaging framework can be extended to simulate various types of failures that happen in real production distributed systems. You will use chaos engineering techniques to find flaws in a system even before it gets live.

You will also experience how out-of-order message delivery can wreck havoc in message de-duplication strategies that otherwise seem perfect. Last, but not least, you will learn how to build practical message de-duplication solution for your distributed system. 

## Agenda

- Distributed asynchronous systems - why bother?
- Idempotent business logic
- Chaos engineering
- Simulating failures in the running system
- Messages are always delivered in order, aren't they?
- Simulating out-of-order delivery
- Message identity and identity-based de-duplication
- Outbox

## Structure

The workshop consists of interleaved lectures and practical exercises. The purpose of the exercises is for you to experience the problems first hand while the lectures are there to give you the contextual information and explanation. The exercises are designed to be chained together as each exercise builds upon the the previous one. They are difficult and that's by design. It's not a simple copy-paste thing. The goal is for you to struggle with them at least a bit. But don't worry if you get lost midway through. There is a collection of prepared starting points so if you get stuck in one exercise, you will still be able to start working on the next one.

## Prerequisites

The workshop exercises are prepared in C# and .NET however we will not be using advanced features of the language/platform so it should be accessible even for developers that don't have C#/.NET background. The exercise starting points already contain references to all required libraries (NuGet packages) and, whenever possible, we will stick to basic C# constructs.

Below is the list of required software. All three apps are free/have free versions.

- SQL Server Management Studio - [download](https://docs.microsoft.com/en-us/sql/ssms/download-sql-server-management-studio-ssms?view=sql-server-2017)
- SQL Server Express - [download](https://www.microsoft.com/en-us/sql-server/sql-server-editions-express)
- Visual Studio 2019 - [download](https://visualstudio.microsoft.com/pl/downloads/)

## About me

My name is Szymon Pobiega. I used to work on various business software for almost a decade. Of all the ideas and patterns I learnt along the way, messaging had the most profound impact. I designed my first micro service system with MSMQ and NServiceBus 1.9 some 10 years ago and this was a life-changing experience.

Fire years ago I quit consulting and joined Particular Software with hope to use his field experience to make NServiceBus even better. Szymon is focused, in Particular (pun intended), on message routing patterns and handling of failures. 

During that the last five years I spent a great deal of my time helping developers deal with issues related to communication in distributed systems. This workshop is based on the real-world problems that people were struggling with.

Besides that, in my free time I enjoy building remotely controlled vehicles with Lego.


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

## Lecture: Message ID

## Exercise 7: ID-based de-duplication

## Exercise 8: Deterministic IDs

## Exercise 9: Even more chaos

## Lecture: Outbox

## Exercise 10: Outbox
