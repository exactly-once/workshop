# Exercise 6: Bring in more chaos

In this exercise we are going to add some delay in our chaos monkey to simulate how messages can be be re-ordered in transit. Previously when the user issued `AddItem` and `RemoveItem` commands, the receiver was guaranteed to see the following sequence: `AddItem`, `AddItem`, `RemoveItem`, `RemoveItem`. With we add delay sequences such as `AddItem`, `RemoveItem`, `RemoveItem`, `AddItem` will be possible.

- In the `Frontend` endpoint implement sending in a fire-and-forget manner by wrapping the `endpoint.Send` call in a `Task.Run`.
  - Ignore the warning
- Modify the behavior that duplicates outgoing messages
  - If the `Item` type is `Mushrooms` execute code that waits for 10 seconds (via `Task.Delay`) and then creates a duplicate (by invoking `await next()`)
- Test the system by requesting adding and removal of `Mushrooms` quickly