using System.Linq;
using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;

class RemoveItemHandler : IHandleMessages<RemoveItem>
{
    OrderRepository orderRepository;

    public RemoveItemHandler(OrderRepository orderRepository)
    {
        this.orderRepository = orderRepository;
    }

    public async Task Handle(RemoveItem message,
        IMessageHandlerContext context)
    {
        var order = await orderRepository.Load(message.OrderId);

        var lineToRemove = order.Lines.FirstOrDefault(x => x.Filling == message.Filling);

        if (lineToRemove == null)
        {
            log.Info("Potential duplicate RemoveItem message detected.");
        }
        else
        {
            order.Lines.Remove(lineToRemove);

            await orderRepository.Store(order);

            log.Info($"Item {message.Filling} removed.");
        }

        await context.PublishImmediately(
            new ItemRemoved(message.OrderId, message.Filling));

    }

    static readonly ILog log = LogManager.GetLogger<RemoveItemHandler>();
}