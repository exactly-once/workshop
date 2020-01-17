using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;

public class ItemRemovedHandler : IHandleMessages<ItemRemoved>
{
    public Task Handle(ItemRemoved message, IMessageHandlerContext context)
    {
        log.Info($"Message {context.MessageId}: Item of type {message.Filling} removed from order {message.OrderId}");
        return Task.FromResult(0);
    }

    static readonly ILog log = LogManager.GetLogger<ItemRemovedHandler>();
}