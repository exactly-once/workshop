using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;

class SubmitOrderHandler : IHandleMessages<SubmitOrder>
{
    OrderRepository orderRepository;

    public SubmitOrderHandler(OrderRepository orderRepository)
    {
        this.orderRepository = orderRepository;
    }

    public async Task Handle(SubmitOrder message, IMessageHandlerContext context)
    {
        if (await orderRepository.Load(message.OrderId) != null)
        {
            log.Info("Duplicate SubmitOrder message detected. Ignoring");
            return;
        }

        var order = new Order
        {
            Id = message.OrderId
        };

        await orderRepository.Store(order);

        log.Info($"Order {message.OrderId} created.");
    }

    static readonly ILog log = LogManager.GetLogger<SubmitOrderHandler>();
}