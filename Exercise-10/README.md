# Exercise 10: Non-deterministic message generation

After our previous change, the system behaves stable. Mostly. In response to new requirements an additional event type has been added -- `FirstItemAdded`. This event is published when the customer adds first item to their orders. It is used by the marketing department to study the buying habits. Unfortunately from time to time they notice the lack of `FirstItemAdded` event. What could have gone wrong? The problem seems to be correlated with timeouts. We are going to investigate this by first trying to reproduce the problem using another *chaos monkey*. 

In this exercise we are going to extend the `BrokerErrorSimulatorBehavior` by adding another `if` clause that checks if the outgoing message is of type `FirstItemAdded`. In that case we will simulate a timeout error by waiting for 10 seconds **and then throwing an exception**. We hope that this is exactly what the operations team have seen in production.

We will examine the behavior of our code by using a brand new type of *pierogi*. Try adding two items of type `Strawberry` quickly. What happens?
