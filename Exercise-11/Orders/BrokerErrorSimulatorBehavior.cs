using System;
using System.Threading.Tasks;
using Messages;
using NServiceBus.Pipeline;

class BrokerErrorSimulatorBehavior : Behavior<IOutgoingLogicalMessageContext>
{
    bool failed;

    public override async Task Invoke(IOutgoingLogicalMessageContext context, Func<Task> next)
    {
        if (!failed && context.Message.Instance is ItemAdded {Filling: Filling.QuarkAndPotatoes})
        {
            failed = true;
            throw new Exception("Broker failure");
        }

        if (!failed && context.Message.Instance is FirstItemAdded firstItem)
        {
            failed = true;
            await Task.Delay(10000, context.CancellationToken);
            throw new Exception("Timeout");
        }
        await next();
    }
}