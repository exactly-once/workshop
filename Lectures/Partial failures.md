# Partial failures

### Anomalies we know

If delivering a message to its destination once can be called a norm then so far we've already seen a number of anomalies, some of them expected while others -- not. After the morning lecture we did expect duplicates, didn't we? 

### Anomalies we didn't know

What we were not prepared to deal with were missing downstream messages and ghost messages. These two anomalies are caused by defects in handling the side effects of message processing. The challenge that we did not discuss in the morning was coordinating the data manipulation and message publishing.

### Coordinating data manipulation

How come we missed it? Well, we talked how **A** is going to execute data manipulation `X` and send message `b` but we didn't explored how **A** is going to coordinate these two activities and especially how **A** is going to handle failure modes. We are dealing here with two separate transactional resources, the queue and the database. As you recall, we talked today multiple times that it is impossible to guarantee that these two will be modified atomically. We need to deal with *partial failures*. How can we proceed then?

### Not all resources are created equal

Let's take a look at the nature of our transactional resources. As it turns out, there are some substantial differences that we can exploit

### Likelihood of rejection

The main difference lies in the likelihood that a given proposed transaction is rejected. There are multiple possible reasons why a change `X` might fail. Some of them are transient e.g. database server crash but in these cases retrying the attempt is going to eventually unblock us. Unfortunately there is a second category of failures that are persistent and cause the proposed transaction (data modification `X`) to be rejected no matter how many times we try. Validation rules are a good example here.

When it comes to a queue the persistent failures are much less likely. The only reason why a message send transaction might be rejected is incompatibility with the message infrastructure e.g. a message is too big. 

### Consequences to the logic

Another difference is the most likely cause of persistent rejection. For a database that is validation error while for the queue it is infrastructure incompatibility.

### The order

There are obviously two possible orders of execution of *update data* (U) and *publish messages* (P) actions: UP and PU. Our goal here is to minimize the likelihood and duration of states in which one of the actions is applied and the other is not: U or P. 

Given that P is less likely to fail persistently, we should favour UP, not PU. There is one more reason why UP is more desirable. In UP, if P is persistently rejected then we are dealing with a business process that remains correct but stuck at one of the stages. If we adopted PU and U was rejected persistently then we would have an uninterrupted business process execution but that process would be in an inconsistent state. In most real-life scenarios it is much better to be stuck than wrong.

Now I think we are ready to define the structure of a handler logic.
 - Check if a given data change has already been applied (does the order have an item of that type?)
   - If no then execute the business logic that applies the change
 - Commit the data store transaction that applies the change
   - The database needs to enforce the same rules as used to detect if change has already been applied to prevent two concurrent processes from making a mess
 - Regardless if a given change has been applied or not, publish outgoing messages that should be published when that type of change is applied.

As you can see now, the order of operations that we arrived at by means to trial and error can indeed be explain by more "engineering" type of reasoning.