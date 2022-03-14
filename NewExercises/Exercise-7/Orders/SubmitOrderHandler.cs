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
        var order = new Order
        {
            Id = Guid.NewGuid().ToString(),
            Customer = message.Customer,
            Items = message.Items
        };

        await repository.Put(message.Customer, (order, null));

        log.Info("Order submitted "+ order.Id);
    }

    static readonly ILog log = LogManager.GetLogger<SubmitOrderHandler>();
}