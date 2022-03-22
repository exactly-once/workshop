# Exercise 6 - The USB Rule

It is a well-known fact that the classic USB plug never fits the first time. You *always* end up having to turn it around only to conclude that it still doesn't fit. Third time's a charm, so when you turn it around again, somehow it fits. Scientists are still working on explaining that phenomenon ;-)

On a serious note, what we have observed in the previous exercise was a lost message, or what we also call a **phantom record**. We updated the state first and then sent the message. If the latter fails, the state is already modified. At that point, the view shows a submitted shopping cart even though the submission message never went out. Therefore, the submitted cart represents a phantom record, because the according message was lost. What can we do? 

We can use the USB principle and try to switch the order of the operations. If we first try to send the message and then update the state, we ensure that if the send fails, the customer will continue to see an unsubmitted shopping cart, at which point they will hopefully try to submit the order again.

- In the `ApplicationServices` class, change the `SubmitOrder` method to reverse the order of `repository.Put` and `session.Send`. This should ensure that the cart never appears as `Submitted` if the sending the message fails.
- Check if the system can handle the simulated broker failures correctly.
- Now go on add add few (4-5) more orders. Let's see what happens.