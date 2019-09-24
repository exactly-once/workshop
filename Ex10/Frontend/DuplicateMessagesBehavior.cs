using System;
using System.Threading.Tasks;
using Messages;
using NServiceBus.Pipeline;

class DuplicateMessagesBehavior : Behavior<IOutgoingLogicalMessageContext>
{
    public override async Task Invoke(IOutgoingLogicalMessageContext context, Func<Task> next)
    {
        if (context.Message.Instance is AddItem addItem)
        {
            if (addItem.Filling == Filling.Meat)
            {
                await next();
            }
            else if (addItem.Filling == Filling.Mushrooms)
            {
                await next();
                await Task.Delay(TimeSpan.FromSeconds(10));
            }
        }
        await next();
    }
}