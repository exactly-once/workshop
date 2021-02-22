## Requirements

- [Visual Studio Code](https://code.visualstudio.com/)
- [TLA+ extensions](https://github.com/alygin/vscode-tlaplus/wiki/How-to-Install)
 

## Introduction

`MessageHandler.tla` holds a TLA+ specification of a message processing handler. It models an environment with no distributed transactions available i.e. messaging infrastructure and the business data store operations are performed without any atomicity guarantees. 

## Exercise 1

Model-checking with TLA+ requires two elements, a specification (`MessageHandler.tla`) and model checker configuration (`MessageHandler.cfg`). 

To run the model checker we need to:
 * Parse the specification: <kbd>Ctrl</kbd>+<kbd>Shift</kbd>+<kbd>P</kbd> -> `TLA+: parse module`
 * Check the model: <kbd>Ctrl</kbd>+<kbd>Shift</kbd>+<kbd>P</kbd> -> `TLA+: check the model with TLC`

 This opens `TLA+ model checking` window that shows the model checking status and the final result.

## Exercise 2

Let's verify that the model does not allow for ghost messages using `NoGhostMessages` formula:

```tla+
NoGhostMessages == \A m \in processed : 
                        \/ ~ \E msg \in queueOut : msg.id = m.id
                        \/   \E chg \in db       : chg.id = m.id
```

In the Visual Studio code:
 * Open `MessageHandler.cfg` and add `NoGhostMessages` in the `INVARIANTS` section of the file.
 * Parse and model-check the specification.
 * The check fails with:
    > Invariant NoGhostMessages is violated.
 * Analyze the trace to understand in what scenario ghost messages can happen. 
 * Change the order of steps in the handler specification to prevent ghost messages.

## Exercise 3

Let's verify that the model does not allow any outgoing messages to be lost using `NoLostMessages` formula:

```tla+
NoLostMessages == \A m \in processed :
                        \/ ~ \E chg \in db       : chg.id = m.id
                        \/   \E msg \in queueOut : msg.id = m.id
```

 * Open `MessageHandler.cfg` and add `NoLostMessages` in the `INVARIANTS` sections.
 * Parse and model check the specification.
 * The check fails with:
    > Invariant NoGhostMessages is violated.
 * Analyze the trace to understand what happened
 * Let's patch the problem temporarily and change the atomicity of the steps (this models 2PC) to prevent outgoing message loss

```tla+
UpdateDbAndSend: (* update data base and send output messages - can fail *)
    either Fail(msg.id);
    or db := db \union {[id |-> msg.id, ver |-> c]}; 
       queueOut := queueOut \union {[id |-> msg.id, ver |-> c]};
    end either;
```

## Exercise 4

Let's verify that the model does not allow for duplicated processing of the same message using `NoDuplicatedProcessings` formula:

```tla+
NoDuplicatedProcessings == \A a \in db:
                            ~ \E b \in db : a.id = b.id /\ a.ver /= b.ver
```

 * Open `MessageHandler.cfg` and add `NoDuplicatedProcessings` in the `INVARIANTS` sections.
 * Parse and check the specification.
 * Analyze the trace.
 * Change the specification to prevent duplicated processing based on the database state. The message should be processed only when the DB does not hold a change for that logical message.

``` TLA+
if ~\E chg \in db : chg.id = msg.id then
    ...
end if;
```
## Exercise 5

Now we want to keep current properties but remove the atomicity between database updates and sending out messages: 
 * First, we will make a change to the specification. Currently, our model allows for a message to be partially processed due to failures. We will change it so that every message is eventually processed - possibly with some failures. 
 * Add `Fails(messageId)` definition at the top of the `define` section.

```tla+
Fails(messageId) == IF messageId > MaxFailures THEN {TRUE, FALSE} ELSE {FALSE}
```
 * Change the `Fail` macro to update the number of failures for a given message and jump back to the `MainLoop` label

```tla+
macro Fail(messageId) begin
    failures[messageId] := failures[messageId]+1;
    goto MainLoop;
end macro;
```
 * Split `UpdateDbAndSend` lables back into two separate labels.
 * Change specification in the `UpdateDb` and `Send` and `AckInMsg` labels to model the fact that there can be up to`MaxFailuers` for any given message. E.g:

```tla+
UpdateDb:
    with fails \in Fails(msg.id) do
        if fails then
            Fail(msg.id)
        else
            if ~\E chg \in db : chg.id = msg.id then
                db := db \union {[id |-> msg.id, ver |-> c]}; 
            end if;
        end if;
    end with;
```
 * Parse and model-check the specification.

 HINT: Should we do `if ~\E chg \in db: ...` check in the message sending step?

## Exercise 6

Let's make the model a bit bigger
 * Change model to allow for up to 4 failures.
 * Parse and check the specification.

## Exercise 7

Let's check that the handler returns a consistent output using following formula:

``` tla+
ConsistentOutput == \A m1 \in queueOut:
                        ~\E m2 \in queueOut: m1.id = m2.id /\ m1.ver /= m2.ver
```

 * Add the `ConsistentOutput` formula definition to the specification.
 * Add `ConsistentOutput` to the `INVARIANTS` section.
 * Parse and model check the specification.
 * Analyze the failing trace.
 * Change the `Send` label part to make sure that the output messages are sent with consistent version based on the DB state.

 HINT: You can get the version of the DB change for given message id using `with` statement:

 ``` tla+
with chg \in {chg \in db : chg.id = msg.id} do
    (* chg is available in this block *)
end with;
 ```

## Exercise 8

Let's talk about what is not in the model :).