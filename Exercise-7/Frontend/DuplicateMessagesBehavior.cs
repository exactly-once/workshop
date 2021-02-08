using System;
using System.Threading.Tasks;
using Messages;
using NServiceBus.Pipeline;

class DuplicateMessagesBehavior : Behavior<IOutgoingLogicalMessageContext>
{
    public override async Task Invoke(IOutgoingLogicalMessageContext context, Func<Task> next)
    {
        await next();
        if (context.Message.Instance is AddItem addMeat && addMeat.Filling == Filling.Meat)
        {
            await next();
        }
        else if (context.Message.Instance is AddItem addMushrooms 
                 && addMushrooms.Filling == Filling.Mushrooms)
        {
            await Task.Delay(TimeSpan.FromSeconds(10));
            await next();
        }
        
    }
}