# Exercise 7 - If in doubt, try again

What you have observed in the previous exercise were **ghost messages**. These messages carry information about state changes that were never applied. Ghost messages are equally harmful as phantom records. They can easily turn a system that was supposed to be eventually consistent into an immediately inconsistent one. We need to solve this problem.

The solution is to revert our changes to a the save-first, send-later approach (remember the USB principle?). However, this time we allow re-sending the submit message. To ensure it is safe to do it we'll introduce a new status of the shopping cart -- `Accepted`. We mark the cart as accepted before attempting to send a message and we mark it as submitted once we know at least one copy of the message has been successfully sent.

- Notice we have added a new `Accepted` flag to the shopping cart. It will be used in the submit logic.
- In the `ApplicationServices` class and change the logic of the `SubmitOrder` method to do the following:
  - If the cart is submitted, throw an exception (as previously).
  - If the cart is accepted:
    - send the `SubmitOrder` message,
    - set the state of the shopping cart to submitted,
    - save the state of the shopping cart.
  - If the cart is not yet accepted:
    - set the state of the shopping cart to accepted,
    - save the state of the shopping cart,
    - send the `SubmitOrder` message,
    - set the state of the shopping cart to submitted,
    - save the state of the shopping cart.

Consider the consequences of this behavior to the`Orders` service. What would happen if `AddItem` was called when the shopping cart is in the accepted state?
