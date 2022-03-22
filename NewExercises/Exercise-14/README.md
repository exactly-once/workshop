## State-based message generation

Now that we can reliably calculate the total of all payments made by a customer, the business wants to put this information to good use. 
Our team needs to add a small feature i.e. when a customer exceeds 100 USD in total payments, we want to send them a coupon. 
 
* In the `IssueCouponCardAfterFirst100USDSpent` test, define the following sequence of message processing:
 
```csharp 
new IMessage[] { 
  submitFirstOrder, 
  bookFirstPayment, 
  submitSecondOrder, 
  bookSecondPayment 
} 
``` 
What could be a production scenario in which this could happen?

* Run the test and check if the assertion holds 
* Add logic in the `DropMessagesBehavior` to ensure that the `GrantCoupon` message is discarded the first time it is sent. This simulates a situation when `PaymentBookHandler` fails when sending out `GrantCoupon` and the incoming message is retried. Use the same method as in [Exercise 5](../Exercise-5/README.md):
  * Add a boolean flag `dropped`
  * In the `Invoke` method, check if the `context.Message.Instance` is `GrantCoupon`. If so, and the flag is `false`, flip the flag and return. Otherwise, invoke `await next()`. This logic will ensure that only the first instance of the `GrantCoupon` message is dropped.
* To account for this simulated failure, we will add an additional copy of the `bookFirstPayment` to the messages list for the test:

```csharp 
new IMessage[] { 
  submitFirstOrder, 
  bookFirstPayment, 
  submitSecondOrder, 
  bookSecondPayment, 
  bookFirstPayment //HINT: this is a retried message 
} 
``` 

* With that change in place, the test should pass again. Re-run the test. Does it work? Can you tell why? Try placing some breakpoints in the `PaymentBookedHandler`:
   * on line 18 to check how many times the handler is invoked
   * on line 36 to see how many times the business logic is invoked
   * on line 38 to see how many times the `GrantCoupon` message is generated
* Can you explain the behavior?
* Use a `public List<ICommand> OutgoingMessages = new List<ICommand>();` property in the `Payments` entity to store the outgoing messages.
* Instead of sending the message immediately, on line 38, add it to the `OutgoingMessages` collection.
* Make sure that items in the `OutgoingMessages` are _always_ sent out (including the cases in which a duplicate is detected). Add the following code to the bottom of the handler:
 
```csharp 
foreach (var outgoingMessage in payments.OutgoingMessages) 
{ 
    await context.SendImmediately(outgoingMessage); 
} 
``` 
* Run all the tests in the `Tests` project.
