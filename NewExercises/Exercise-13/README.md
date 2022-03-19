## Deterministic message identifiers

Due to considerable sucess of our the business, the system has been extended with new `Marketing` endpoint, reponsible for tracking value of payments booked for any given customer. Now when status of an order is changed either `PaymentBooked` or `PaymentCancelled` event is published.  
 
Unfortunatelly, our production support team claims that once in a while the calculated value for a customer does not match the total from all the payments. Let's see if we can reproducte such a scenario. 
 
* Go to `TrackTotalPaymentsValue` test and check if it passes. Why does it fail? Check what is are the `MessageId` values for both duplicates of the `BookPayment` message. Why are they different? 
* In the `BookPaymentHandler` and `CancelPaymentHandler` use `PublishWithId` extension method and use `Utils` class to ensure that the published messages have ids that are deterministically derived from the incoming message id and the endpoint name. 
* Why do we need to put the endpont name in there? 
* Ensure that both tests are passing 
