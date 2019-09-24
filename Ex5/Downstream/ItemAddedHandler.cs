using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;

public class ItemAddedHandler : IHandleMessages<ItemAdded>
{
    public Task Handle(ItemAdded message, IMessageHandlerContext context)
    {
        log.Info($"Item of type {message.Filling} added to order {message.OrderId}");
        return Task.FromResult(0);
    }

    static readonly ILog log = LogManager.GetLogger<ItemAddedHandler>();
}
