### Exercise 1 - a simple web app
 - Shopping cart with items
 - AddItem button to add pierogi
 - Order -> Creates a new entity called Order

Follow up: what happens if you click "Order" twice quickly? Two orders.

### Exercise 2 - deduplicate order processing with a flag

 - Add a flag "Submitted" to the shopping cart
 - Changes the flag to true when creating order - state-based deduplication

Follow up: what happens if you click "Order" twice _very_ quickly? Two orders

### Exercise 3 - optimistic concurrency

 - Add optimistic concurrency checks

### Exercise 4 - make it async - handle a message

Introduction to messaging - asynchronous processing, distributed systems etc.

 - Order button flips a flag and sends a message and a handler creates the order

Uses a solution similar to the current Ex 14 - after the sync/async boundary.

### Exercide 5 - simulate broker problems

Add behavior that simulates problems when sending out a message. As a result the flag is flipped (order submitted) but no message is sent.

### Exercise 6 - change the order of operations

Switch to save+publish. Looks good. Try adding pierogi with swiss cheese. Validation error but order processed. Not good. Ghost message.

### Exercise 7 - remove the anomalies

We need to use the save+(re)publish approach to avoid message loss and ghost messages. But how to drive the re-publish? HTTP->messaging gatway. When Order is clicked, just send a message. The flag flip is going to be in a message handler now, not in the controller.

### Exercise 8: Duplicates on the receiver (lock timeout)

The solution now uses the ASQ transport and there. Put the delay in the Process order handler.

### Exercise 9: Duplicates on the sender side (broker issues causing re-publish)

Enable the broker issue chaos monkey again. See how dupicate process order messages are sent.

### Exercise 10: Business ID-based deduplication

Create-type operation can be de-duplicated based on the ID of the entity/aggregate to be created. Add such logic to the order. And test.

### Exercise 11, 12 and 13 - customer status policy

Using a different solution that only has the policy endpoint. Using the acceptance testing framework.

 - SubmitOrder -> OrderSubmitted
   - Idempotent operations not idempotent when re-ordering -> use message IDs
   - ID-based deduplication only good if IDs are stable
   - Deterministic state

### Summary

 - State-based deduplication at the boundary of the system - requires optimistic concurrency
 - ID-based de-duplication only good when creating entities 
 - Idempotent operations are not idempotent when re-ordering is allowed
 - Message-id based deduplication requires deterministic IDs
 - No deduplication method is correct when the state of the object is allowed to change between the duplicated messages

### Exercise 14: Outbox (previously exercise 12 - generic outbox)

Back to a simple solution for exericese 10.

### Exercise 15: Outbox with Inbox (previously exerice 13 - inbox)

