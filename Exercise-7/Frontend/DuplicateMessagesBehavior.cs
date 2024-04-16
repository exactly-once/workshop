using System;
using System.Threading.Tasks;
using Messages;
using NServiceBus.Pipeline;

class DuplicateMessagesBehavior : Behavior<IOutgoingLogicalMessageContext>
{
    public override async Task Invoke(IOutgoingLogicalMessageContext context, Func<Task> next)
    {
        await next();

        if (context.Message.Instance is AddItem { Filling: Filling.Meat })
        {
            await next();
        }
        else if (context.Message.Instance is RemoveItem { Filling: Filling.Meat })
        {
            await next();
        }
    }
}