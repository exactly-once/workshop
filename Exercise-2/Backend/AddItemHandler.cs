using System.Linq;
using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;

class AddItemHandler : IHandleMessages<AddItem>
{
    OrderRepository orderRepository;

    public AddItemHandler(OrderRepository orderRepository)
    {
        this.orderRepository = orderRepository;
    }

    public async Task Handle(AddItem message, 
        IMessageHandlerContext context)
    {
        var order = await orderRepository.Load(message.OrderId);

        var line = new OrderLine(message.Filling);
        order.Lines.Add(line);
        log.Info($"Item {message.Filling} added.");

        await context.PublishImmediately(
            new ItemAdded(message.OrderId, message.Filling));

        await orderRepository.Store(order);
    }

    static readonly ILog log = LogManager.GetLogger<AddItemHandler>();
}