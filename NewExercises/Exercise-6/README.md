# Exercise 6 - The USB Rule

It is a well-known fact that the classis USB plug never fits the first time. You *always* have to turn it around but it does not fit either. Then you turn it around again and it fits. Scientists are still working on explaining that phenomenon ;-)

Back to being serious, what we have observed in the previous exercise was a lost message. Because we first update the state and then send a message, if the latter fails, the state is already modified. The customer sees their shopping cart as submitted even though the submission message never went out. What can we do? 

We can use the USB principle and try to turn the order of operations upside-down. If we fist try to send the message and then update the state, we will make sure that if the send fails, the customer will see the correct state of the shopping cart and hopefully will retry the submission.

- Go to the `ApplicationServices` class and the `SubmitOrder` method and reverse the order of `repository.Put` and `session.Send`. This should make sure that the state of the cart remains not `Submitted` if the message sending failed.
- Check if the system can handle the simulated broker failures correctly.
- Now go on add add few (4-5) more orders. Let's see what happens.