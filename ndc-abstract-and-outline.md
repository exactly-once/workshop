How to build fault-tolerant distributed systems when throwing away consistency is not an option

## Elevator pitch

Building fault-tolerant distributed systems that maintain full consistency is not an easy thing. What makes it even harder is lack of solid infrastructure foundations like distributed transactions. Forget about them. Learn to build reliable system from unreliable components available in the cloud.

## Description

The workshop focuses on building line-of-business fault-tolerant cloud-based distributed systems. Such systems cannot afford to lose messages (nobody wants their order for Christmas gifts to be lost) nor to get them duplicated (that second Porsche in the drive way -- who ordered that?). Such systems were, in the past, built based on the firm ground established by either distributed transactions or large database instances that served also as messaging brokers.

These technologies are either too expensive, too cumbersome or simply not available in the cloud. In this workshop we will show how one can deal with the consistent messaging problem by de-duplicating messages.

Join us in the series of ten hands-on exercises interleaved with short lectures after which you'll have good understanding of most of the things that can go wrong when processing messages and enough knowledge to either build build a bullet-and-duplicate-proof message processor or (even better) find a framework that implements one for you.

## Agenda 

TBD

## What will you learn

TBD

## Structure

The workshop consists of interleaved lectures, role-play games and hands-on coding exercises. The purspose of each lecture is to provide you with some background information e.g. what _chaos engineering_ is. Next up, the game session is meant to visualize interaction of system's component in a given scenario. We use the game to explore the boundaries of a given scenario i.e. show what can happen if one of the components breaks down or misbehaves. Together with the audience we try to adjust the rules of the game to mitigate the problem we discovered. Finally, we pair up in front of computers to implement the fix we prototyped in the game.

The coding exercises are designed to be chained together as each exercise builds upon the the previous one. They are difficult and that's by design. It's not a simple copy-paste thing. The goal is for you to struggle with them at least a bit. But don't worry if you get lost midway through. There is a collection of prepared starting points so if you get stuck in one exercise, you will still be able to start working on the next one.

## Prerequisites

The workshop exercises are prepared in C# and .NET however we will not be using advanced features of the language/platform so it should be accessible even for developers that don't have C#/.NET background. The exercise starting points already contain references to all required libraries (NuGet packages) and, whenever possible, we will stick to basic C# constructs.

Below is the list of required software. All three apps are free/have free versions.

- SQL Server Management Studio - [download](https://docs.microsoft.com/en-us/sql/ssms/download-sql-server-management-studio-ssms?view=sql-server-2017)
- SQL Server Express - [download](https://www.microsoft.com/en-us/sql-server/sql-server-editions-express)
- Visual Studio 2019 - [download](https://visualstudio.microsoft.com/pl/downloads/)
