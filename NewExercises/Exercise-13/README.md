## Deterministic message identifiers

Due to the success of our the business, the system has been extended with a new `Marketing` endpoint, responsible for tracking the total expenditure of our customers (the total of all payments). 
When the status of an order is changed, either `PaymentBooked` or `PaymentCancelled` event is published.  
 
Unfortunately, our support team claims that once in a while, the calculated total expenditure per customer does not match the actual total of all payments. Let's see if we can reproduce such a scenario. 

* Go to the `BookPaymentHandler` or `CancelPaymentHandler` and consider the logic. Notice that it is mostly identical to the logic in the previous exercise but it includes events being published. Notice that the basic structure remains the same regardless of the deduplication mechanism used:

```
if (!IsDuplicate()) 
{
   ExecuteBusinessLogic();
   MarkAsDuplicate();
   PersistState();
}
SendAndPublishMessages()'
```
 
* Check if the `TrackTotalPaymentsValue` test passes. Why does it fail? Open the results of the test run and check the `messageId` values for both duplicates of the `BookPayment` message. Why are they different? Does this resemble any situation we've seen before?
* In the `BookPaymentHandler` and `CancelPaymentHandler`, use the `PublishWithId` extension method and the `Utils` class to ensure that the published messages have Ids that are deterministically derived from the incoming message Id. 
* Is our deterministic Id generation strategy a good solution? 
* Does the `ChangeStatus` test still pass?
