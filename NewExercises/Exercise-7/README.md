# Exercise 7 - If in doubt, try again

What you have seen in the previous exercise were ghost messages. These messages carry information about state changes that have not been persisted. Ghost messages are as bad as missing messages because they can easily turn a system that was supposed to be eventually consistent into an immediately inconsistent one. We need to solve this problem.

The solution is to go back to the previous save-fist, send-later approach (remember the USB principle?) but this time allow re-sending the submission message. To make sure it is safe to do it we'll introduce another state of the shopping cart -- `Accepted`. We mark the cart as accepted before attempting to send a message and we mark it as submitted after we know at least one copy of the message has been sent.

- Notice we have added a new `Accepted` flag to the shopping cart. It will be used in the submission logic.
- Go to the `ApplicationServices` class and change the logic of the `SubmitOrder` method to do the following:
  - If the cart is submitted throw an exception (as previously).
  - If the cart is accepted
    - send the `SubmitOrder` message,
    - set the state of the shopping cart to submitted,
    - save the state of the shopping cart.
  - If the cart is not yet accepted
    - set the state of the shopping cart to accepted,
    - save the state of the shopping cart,
    - send the `SubmitOrder` message,
    - set the state of the shopping cart to submitted,
    - save the state of the shopping cart.
- Check what are the consequences of this behavior to the `Orders` service.

Consider what would happen if `AddItem` was called when the shopping cart is in the accepted state.
