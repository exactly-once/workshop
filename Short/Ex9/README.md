# Exercise 9: Deterministic message generation

In this exercise we are going to extend the `BrokerErrorSimulatorBehavior` by adding another `if` clause that checks if the outgoing message is of type `FirstItemAdded`. In that case we will simulate a timeout error by waiting for 10 seconds and then throwing an exception. We hope that his is exactly what the operations team have seen in production.

We will examine the behavior of our code by using a brand new type of pierogi. Try adding two items of type `Strawberry` quickly. What happens?
