using System;
using System.Collections.Concurrent;
using System.Threading.Tasks;
using Messages;
using NServiceBus.Pipeline;

class BrokerFailureToAckBehavior : Behavior<IIncomingLogicalMessageContext>
{
    ConcurrentDictionary<string, bool> cache = new ConcurrentDictionary<string, bool>();

    public override async Task Invoke(IIncomingLogicalMessageContext context, Func<Task> next)
    {
        await next();
        if (context.Message.Instance is AddItem add && add.Filling == Filling.QuarkAndPotatoes)
        {
            if (!cache.ContainsKey(context.MessageId))
            {
                cache.AddOrUpdate(context.MessageId, true, (_, __) => true);
                await Task.Delay(TimeSpan.FromSeconds(10));
                throw new Exception("Broker error");
            }

            cache.TryRemove(context.MessageId, out _);
        }
    }
}
