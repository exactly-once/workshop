## State based message generation

Now that we can reliably calculate value of all the payments made by a customer the business wants to put that to a good use. Our team needs to add a small feature ie. when a customer goes over 100 USD in total paymets for the first time we want to send them a coupon. 
 
* To to `IssueCouponCardAfterFirst100USDSpent` test and define the follwong sequence of message processing. What could be a production scenario in which this could happen? 
 
```csharp 
new IMessage[] { 
  submitFirstOrder, 
  bookFirstPayment, 
  submitSecondOrder, 
  bookSecondPayment, 
  bookFirstPayment //HINT: this is a retried message 
} 
``` 
 
* Run the test and check if the asserition holds 
* Put logic in the `DropMessagesBehavior` to ensure that the `GrantCoupon` message is skipped (dropped) the firt time it is sent. This simulates situation when `PaymentBookHandler` failes on sending out `GrantCoupon` and the incoming message is retried. 
* Re-run the test. Does it work? Why? 
* Use `public List<ICommand> OutgoingMessages = new List<ICommand>();` property in the `Payments` entity to store the outoging messages and save them atomically together with the business changes. 
* Make sure that items in the `OutgoingMessages` are always sent. Also, when duplicates arrive: 
```csharp 
foreach (var outgoingMessage in payments.OutgoingMessages) 
{ 
    await context.SendImmediately(outgoingMessage); 
} 
``` 
* Run all the test in the `Tests` project 
