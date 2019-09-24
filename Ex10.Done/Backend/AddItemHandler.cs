using System.Data.Entity;
using System.Linq;
using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;

class AddItemHandler : IHandleMessages<AddItem>
{
    public async Task Handle(AddItem message,
        IMessageHandlerContext context)
    {
        var dbContext = context.Extensions.Get<OrdersDataContext>();

        var order = await dbContext.Orders
            .FirstAsync(o => o.OrderId == message.OrderId);

        if (order.Lines.All(x => x.Filling != message.Filling))
        {
            var line = new OrderLine(message.Filling);
            order.Lines.Add(line);
            log.Info($"Item {message.Filling} added.");

            dbContext.Publish(new ItemAdded(message.OrderId, message.Filling));
        }
    }

    static readonly ILog log = LogManager.GetLogger<AddItemHandler>();
}