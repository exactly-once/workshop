# Exercise 4 - Make it asynchronous

Up until now, we were dealing with a simple web application using a single data store (Cosmos DB). In the meantime, our pierogi-selling application has been overwhelmed with sales and we need to cater for more customers. A common way to adjust applications for scalability purposes is to defer processing and have this handled asynchronously by a dedicated process. This is where you want to start making use of messaging.

In this exercise we are going to move the logic responsible for creating the `Order` aggregate from the web application to a dedicated backend service. Both components are going to communicate using a durable message queue.

Let's get our hands dirty.

- Move the `Order` class from the `WebFrontend` project to the `Orders` project.
- In the `ApplicationServices` class, change the type used by the `GetOrders` method from `Order` to `ShoppingCart`. From now on this method will only list shopping carts. Rename the method to `GetShoppingCarts`.
- In the Orders project, find the `SubmitOrderHandler` class. Notice it implements `IHandleMessages<SubmitOrder>` in order to tell the endpoint that it can handle messages of type `SubmitOrder`.
- Move the code that creates and saves the order from the `SubmitOrder` method to the `Handle` method of `SubmitOrderHandler`.
  - You can now remove the `Task.Delay`. We won't need it any more.
  - Consider logging something at the end of the `Handle` method e.g. `log.Info("Order submitted "+ order.Id);`.
  - Remember that in the `SubmitOrder` method you still need to save the cart after the flag is is set.
- In the `SubmitOrder` method, after the call to `repository.Put` to save the cart, add code to send the `SubmitOrder` message. Use the `session` field of type `IMessageSession` and its `Send` method. Set the properties of the `SubmitOrder` message based on the shopping cart.
- Run the application and check if you can submit an order. Make sure that both `WebFrontend` and `Orders` are selected as start projects.
