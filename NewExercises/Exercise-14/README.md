## State based message generation

Now that we can reliably calculate value of all the payments made by a customer the business wants to put that to a good use. Our team needs to add a small feature i.e. when a customer goes over 100 USD in total paymets for the first time we want to send them a coupon. 
 
* Go to the `IssueCouponCardAfterFirst100USDSpent` test and define the follwong sequence of message processing. What could be a production scenario in which this could happen? 
 
```csharp 
new IMessage[] { 
  submitFirstOrder, 
  bookFirstPayment, 
  submitSecondOrder, 
  bookSecondPayment 
} 
``` 
 
* Run the test and check if the asserition holds 
* Put logic in the `DropMessagesBehavior` to ensure that the `GrantCoupon` message is skipped (dropped) the first time it is sent. This simulates situation when `PaymentBookHandler` failes on sending out `GrantCoupon` and the incoming message is retried. Use the same method as in [Exercise 5](../Exercise-5/README.md):
  * Add a boolean flag `dropped`
  * In the `Invoke` method check if the `context.Message.Instance` is `GrantCoupon`. If so, and the flag is `false` then flip the flag and return. Otherwise invoke `await next()`. This logic will ensure that only the first instance of the `GrantCoupon` message is dropped.
* To account for this simulated failure we should add another copy of the `bookFirstPayment` to the messages list for the test:

```csharp 
new IMessage[] { 
  submitFirstOrder, 
  bookFirstPayment, 
  submitSecondOrder, 
  bookSecondPayment, 
  bookFirstPayment //HINT: this is a retried message 
} 
``` 

* With that change the test should pass again. Re-run the test. Does it work? Can you tell why? Try placing some breakpoints in the `PaymentBookedHandler`:
   * in line 18 to check how many times the handler is invoked
   * in line 36 to see how many times the business logic is invoked
   * in line 38 to see how many times the `GrantCoupon` message is generated
* Can you explain the behavior?
* Use `public List<ICommand> OutgoingMessages = new List<ICommand>();` property in the `Payments` entity to store the outoging messages.
* Instead of sending the message immediately in line 38, add it to the `OutgoingMessages` collection.
* Make sure that items in the `OutgoingMessages` are _always_ sent out (including the times when duplicates arrive). Add following code to the bottom of the handler:
 
```csharp 
foreach (var outgoingMessage in payments.OutgoingMessages) 
{ 
    await context.SendImmediately(outgoingMessage); 
} 
``` 
* Run all the test in the `Tests` project 
