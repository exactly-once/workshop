## Requirements

- [Visual Studio Code](https://code.visualstudio.com/)
- [TLA+ extensions](https://github.com/alygin/vscode-tlaplus/wiki/How-to-Install)
 

## Introduction

`MessageHandler.tla` holds a TLA+ specification of a message processing handler. It models an environment with no distributed transactions available i.e. messaging infrastructure and the business data store operations are performed without any atomicity guarantees. 


## Exercise 1

Model checking with TLA+ requries two elements, a specification (`MessageHandler.tla`) and model checker configuration (`MessageHandler.cfg`). 

To run the model checker we need to:
 * Parse the specification: `Ctrl+Shift+P` -> `TLA+: parse module`
 * Check the model: `Ctrl+Shift+P` -> `TLA+: check the model with TLC`

 This opens `TLA+ model checking` window that shows model checking status and the final result.

## Exercise 2

Let's verify that the model does not allow for ghost messages using `NoGhostMessages` formula:

```tla+
NoGhostMessages == \A m \in processed : 
                        \/ ~ \E msg \in queueOut : msg.id = m.id
                        \/   \E chg \in db       : chg.id = m.id
```

In the Visual Stuido code:
 * Open `MessageHandler.cfg` and add `NoGhostMessages` in the `INVARIANTS` section of the file.
 * Parse and model check the specification.
 * The check fails with:
    > Invariant NoGhostMessages is violated.
 * Analyze the trace to understand in what scenario ghost messages can happen. 
 * Change the order of steps in the handler specification to prevent ghost messages.

## Exercise 3

Let's verify that the model does not allow any outgoing messages to be lost
 * Open `MessageHandler.cfg` and add `NoLostMessages` in the `PROPERTY` sections
 * Check the model
 * Analyze the trace to understand what happened
 * Change the atomicity of the steps to prevent outgoing message loss

## Exercise 4

Let's verify that the model does not allow for duplicated processing of the same message
 * Open `MessageHandler.cfg` and add `NoDuplicatedProcessings` in the `PROPERTY` sections
 * Check the model
 * Analyze the trace
 * Change the specification to prevent duplicated prodessing

``` TLA+
    if ~\E chg \in db : chg.id = msg.id then
        ...
    end if;
```
## Exercise 5

Let's remove the atomicity between database updates and sending outgoing messages
 * Allow at most 4 failures in message processing
 * Keep current properites but remove the atomicity between database updates and sending out messages 

```
   Fails(c) - expression that returns TRUE or FALSE
   if Fails(c)
        Fail()
   else
       ...
```

## Exercise 6

Let's talk about what is not in the modell that makes. 