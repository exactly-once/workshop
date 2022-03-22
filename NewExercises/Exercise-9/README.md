# Exercise 9: Message duplication on the receiver side

In this exercise we are going to experience message duplication first-hand. We'll use [Azure Storage Queues](https://docs.microsoft.com/en-us/azure/storage/queues/storage-queues-introduction) as a messaging infrastructure but the behavior we will observe is not specific to this technology. 

In the solution, complete the following configuration options:
 - Search for "TODO" strings
 - Specify the ASQ connection string
 - Set the endpoint name value to "Orders-_yourname_"
 
The code in this exercise is very similar to the previous exercises but uses a real message queue that we set up in the cloud. Start by running the solution (`Frontend` and `Orders` projects).

- Create one order
- Add some *pierogi* with meat to the order. Is everything OK?

Stop and go back to Visual Studio. Find the `AddItemHandler` class. We are going to simulate lag on the database by inserting a `Task.Delay(40000)` statement, right before the final log statement of the `Handle` method.

- Run the solution
- Create one order
- Add some *pierogi* with meat to the order and wait at least 30 seconds. What happened? Can you explain it?
