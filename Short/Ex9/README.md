# Exercise 9: Deterministic message generation

In this exercise we won't be writing any code. The previous solution has already been modified to include a behavior that simulates broker failures when acknowledging processing of a message -- `BrokerFailureWhenAcknowledgingMessageBehavior`. This behavior is triggered by `Strawberry` items.

The unique thing about the new behavior is the fact that it delays 10 seconds before throwing an exception. This allows other messages to be processed before the initial message that failed can be retried.

The solution includes publishing an event whenever first item is added to a given order. That new feature works for most item types but does not work when you try to add multiple `Strawberry` items. Can you tell why?
