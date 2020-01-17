# Exercise 6: Bring in more chaos

So far the chaos monkey was only able to duplicate each outgoing message. In this exercise we are going to add some random delay to allow the messages to be re-ordered. For example, previously when the user issued `AddItem` and `RemoveItem` commands, the receiver always seen following sequence: `AddItem`, `AddItem`, `RemoveItem`, `RemoveItem`. With added delay sequences such as `AddItem`, `RemoveItem`, `RemoveItem`, `AddItem` will be possible.

- In the `Frontend` endpoint implement sending in a fire-and-forget manner by removing the `await` statement from `endpoint.Send` in the `Send` method.
  - Ignore the warning
- Modify the behavior that duplicates outgoing messages
  - Before invoking `next()` to create a duplicate of `AddItem`, wait for 5 seconds using `Task.Delay`. Do not add delay to duplication of `RemoveItem`
- Test the system by requesting adding and removal of `Mushrooms` quickly