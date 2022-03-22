# Exercise 1 - A simple web application

Let's start simple. The solution contains a very simple "e-commerce" web application that sells pierogi. 

Users must log in by providing their name. Once they are authenticated, they can place items in their shopping cart. Once their shopping cart is ready, they can submit the order for processing.

The domain model of the application consists of two [aggregates](https://martinfowler.com/bliki/DDD_Aggregate.html): `ShoppingCart` and `Order`. The shopping cart is immediately created when a user navigates to the shopping page. Items are added to the cart. Finally, when the user decides to submit the order, the `Order` aggregate is created based on the contents of the `ShoppingCart` aggregate. 

Order processing happens asynchronously via a batch job but is not shown in this simplistic example.

Try placing few orders to get a sense of how the application works. Consider placing some breakpoints, or even breaking the application, to observe the flow.

Consider what happens if you open the same shopping cart in two browser tabs and click `Submit` on both pages? Can you explain the behavior?