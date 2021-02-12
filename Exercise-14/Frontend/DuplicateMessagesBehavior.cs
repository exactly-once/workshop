using System;
using System.Threading.Tasks;
using NServiceBus.Pipeline;

class DuplicateMessagesBehavior : Behavior<IOutgoingPhysicalMessageContext>
{
    public override async Task Invoke(IOutgoingPhysicalMessageContext context, Func<Task> next)
    {
        await next();
        await next();
    }
}