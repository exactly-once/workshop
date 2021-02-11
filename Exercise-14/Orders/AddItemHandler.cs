using System;
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
        var order = context.Extensions.Get<Order>();

        var line = new OrderLine(message.Filling);
        order.Lines.Add(line);
        log.Info($"Item {message.Filling} added.");

        await context.Publish(new ItemAdded(message.OrderId, message.Filling));
        if (order.Lines.Count == 1)
        {
            await context.Publish(new FirstItemAdded(message.OrderId));
        }
    }

    static readonly ILog log = LogManager.GetLogger<AddItemHandler>();
}