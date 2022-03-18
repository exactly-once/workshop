using System;
using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;

class SubmitOrderHandler : IHandleMessages<SubmitOrder>
{
    Repository repository;

    public SubmitOrderHandler(Repository repository)
    {
        this.repository = repository;
    }

    public async Task Handle(SubmitOrder message, IMessageHandlerContext context)
    {
        var (order, version) = await repository.Get<Order>(message.Customer, message.CartId);
        if (version != null)
        {
            log.Info("Duplicate order submission " + order.Id);
            return;
        }
        order = new Order
        {
            Id = message.CartId,
            Customer = message.Customer,
            Items = message.Items,
            Value = PricePerItem * message.Items.Count
        };

        await repository.Put(message.Customer, (order, null));

        log.Info("Order submitted "+ order.Id);
    }

    private const int PricePerItem = 60;

    static readonly ILog log = LogManager.GetLogger<SubmitOrderHandler>();
}