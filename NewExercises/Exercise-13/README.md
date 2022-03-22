## Deterministic message identifiers

Due to considerable sucess of our the business, the system has been extended with new `Marketing` endpoint, reponsible for tracking value of payments booked for any given customer. When status of an order is changed, either `PaymentBooked` or `PaymentCancelled` event is published.  
 
Unfortunatelly, our production support team claims that once in a while the calculated value for a customer does not match the total from all the payments. Let's see if we can reproducte such a scenario. 

* Go to the `BookPaymentHandler` or `CancelPaymentHandler` and take a look at the logic. Notice that it is almost the same as in the previous exercise but it also includes publishing of events. Notice that the basic structure remains the same regardless what type of duplication mechanism is used:

```
if (!IsDuplicate()) 
{
   ExecuteBusinessLogic();
   MarkAsDuplicate();
   PersistState();
}
SendAndPublishMessages()'
```
 
* Go to `TrackTotalPaymentsValue` test and check if it passes. Why does it fail? Open the results of the test run and check what is are the `messageId` values for both duplicates of the `BookPayment` message. Why are they different? Doest it resemble any situation we have seen before?
* In the `BookPaymentHandler` and `CancelPaymentHandler` use `PublishWithId` extension method and use `Utils` class to ensure that the published messages have Ids that are deterministically derived from the incoming message Id. 
* Is our deterministic Id generation strategy good? 
