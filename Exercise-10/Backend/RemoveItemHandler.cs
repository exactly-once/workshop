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

        if (order.ProcessedMessages.Contains(context.MessageId))
        {
            log.Info("Potential duplicate RemoveItem message detected.");
        }
        else
        {
            var lineToRemove = order.Lines.FirstOrDefault(x => x.Filling == message.Filling);
            order.Lines.Remove(lineToRemove);
            order.ProcessedMessages.Add(context.MessageId);
            await orderRepository.Store(order);

            log.Info($"Item {message.Filling} removed.");
        }

        await context.PublishWithId(
            new ItemRemoved(message.OrderId, message.Filling),
            Utils.DeterministicGuid(context.MessageId, "Orders").ToString());

    }

    static readonly ILog log = LogManager.GetLogger<RemoveItemHandler>();
}