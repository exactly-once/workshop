# Definitions

Let's now talk a bit about the context of today's workshop. So far we talked about components **A** and **B** and data modifications X and Y. While it is useful to talk about abstract terms, for actually doing the work we need something more concrete and tangible. 

## Story

I would like you to imagine that you are all part of an engineering team at a startup set out to disrupt the food delivery market, focusing in the first stage on Pierogi. For those of you who might not know, pierogi is a type of dumpling dish well known in central and eastern Europe (though by different names in different countries). Pierogi is the Polish name and I will be using it.

So, we are hired there to build a system for processing Pierogi delivery orders. Besides us, there is also another person hired, The Architect. The architect is there, of course, to design The Architecture that poor developers are going to code. Because The Architect is well-acquainted with most recent developments in the field, he proposes to use a microservice architecture. Whole system should be divided up into small services which communicate by sending or publishing messages. Sounds familiar? Yes, this is exactly the distributed asynchronous approach we talked about so far although the arguments The Architect uses are a bit different than the one I presented. His are "because that's how you do it". Unfortunately after passing on the initial system design blueprints the architect disappears claiming he is busy with other stuff and refuses to answer any specific questions from the engineering team.

## Dictionary

Before we jump head-fist into implementation let me clarify some terms I am going to use. 

### Endpoint

First, the endpoint. The message endpoint (or just endpoint in short) is a type of component that processes messages from a designated queue. Each endpoint is associated with a different queue (queue is exclusive). Endpoints take messages from the queue and pass them to message handlers. A message handler is a component that is able to process a single type of message. Processing a message in a handler may result in data modification in the handler's data store and/or sending/publishing other messages.

Multiple copies of the same endpoint can be deployed in a competing-consumers manner to increase the throughput of processing.

For the purpose of this workshop we'll assume that each endpoint has a separate data store.

### Message

Messages are the means of communication between the endpoints. Each message consists of two parts -- a body (or payload) and headers. The body is the business-relevant part of the message (e.g. the contents of the order). The headers is a bag of additional properties of a message that have no business relevance (e.g. who sent the message, when it was sent etc.). Each message has a type that describes the kind of payload it carries e.g. `SubmitOrder` or `ItemAdded`.

Messages are generally categorized into *Commands* and *Events* but there are at least two different and sometimes conflicting rationales for the categorization. According to one *Commands* carry a request to modify some state whereas *Events* carry an information about state change thaws has happened. As such, *commands* can be *rejected* (the state change is not going to be made) while *events* can't.

According to other sources the difference is based on the cardinality of processors: a *command* has always a single destination while *events* are delivered to all interested parties. In this workshop we'll use the latter version.
