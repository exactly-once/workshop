# Exercise 2: Message duplication on the receiver side

In this exercise we are going to experience the message duplication first-hand. We are going to use Azure Storage Queues as a messaging infrastructure but the behavior we are going to observe is not specific to this technology. 

In the previous exercise we have created our first message handler. The code in this exercise is very similar but uses a "real" message queue that we have set up in the cloud. Start by running the solution (`Frontend` and `Orders` projects).

- Create one order
- Add some *pierogi* with meat to the order. Is everything OK?

Stop and go back to Visual Studio. Find the `AddItemHandler` class. We are going to simulate a slow database by adding a `Task.Delay(40000)` before the final log statement of the `Handle` method.

- Run the solution
- Create one order
- Add some *pierogi* with meat to the order and wait at least 30 seconds. What happened? Can you explain it?