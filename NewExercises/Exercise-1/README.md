# Exercise 1 - A simple web application

Let's start simple. The solution contains a very simple "e-commerce" web application that sells pierogi. 

Users have to log in by providing their name. Then, they can place orders by adding items to a shopping cart and finally submitting the shopping cart for processing.

The domain model of the application consists of two aggregates: `ShoppingCart` and `Order`. The shopping cart is created immediately when a user navigates to the shopping page. Items are added to the cart. Finally, when the user decides to submit the order, the `Order` aggregate is created based on the contents of the `ShoppingCart` aggregate. 

Order processing happens asynchronously via a batch job but is not shown in this simplistic example.

Try placing few orders to get the feeling of the application. Maybe put some breakpoints and see the flow.

Perhaps try to break the application? What happens if you open the same order in two browser tabs and click `Submit` on both pages? Can you explain the behavior?