using System;
using System.Collections.Concurrent;
using System.Threading.Tasks;
using Messages;
using NServiceBus.Pipeline;

class BrokerFailureBehavior : Behavior<IOutgoingLogicalMessageContext>
{
    ConcurrentDictionary<string, bool> cache = new ConcurrentDictionary<string, bool>();

    public override async Task Invoke(IOutgoingLogicalMessageContext context, Func<Task> next)
    {
        if (context.Message.Instance is ItemAdded added && added.Filling == Filling.QuarkAndPotatoes)
        {
            if (context.TryGetIncomingPhysicalMessage(out var incomingMessage))
            {
                if (!cache.ContainsKey(incomingMessage.MessageId))
                {
                    cache.AddOrUpdate(incomingMessage.MessageId, true, (_, __) => true);
                    throw new Exception("Broker error");
                }
                cache.TryRemove(incomingMessage.MessageId, out _);
            }
        }
        await next();
    }
}