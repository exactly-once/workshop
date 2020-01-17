using System;
using System.Threading.Tasks;
using Messages;
using NServiceBus.Pipeline;

class BrokerFailureWhenAcknowledgingMessageBehavior : Behavior<IIncomingLogicalMessageContext>
{
    bool failed;

    public override async Task Invoke(IIncomingLogicalMessageContext context, Func<Task> next)
    {
        await next();

        if (!failed && context.Message.Instance is AddItem added && added.Filling == Filling.Strawberry)
        {
            failed = true;
            await Task.Delay(TimeSpan.FromSeconds(10));
            throw new Exception();
        }
    }
}