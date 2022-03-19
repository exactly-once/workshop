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
        var order = await orderRepository.Load(message.OrderId);

        if (!order.ProcessedMessages.Contains(context.MessageId))
        {
            var line = new OrderLine(message.Filling);
            order.Lines.Add(line);
            log.Info($"Item {message.Filling} added.");

            order.ProcessedMessages.Add(context.MessageId);
            order.OutgoingMessages.Add(Guid.NewGuid().ToString(), new ItemAdded(message.OrderId, message.Filling));
            if (order.Lines.Count == 1)
            {
                order.OutgoingMessages.Add(Guid.NewGuid().ToString(),
                    new FirstItemAdded(message.OrderId));
            }

            await orderRepository.Store(order);
        }

        if (order.OutgoingMessages.Any())
        {
            foreach (var kvp in order.OutgoingMessages)
            {
                await context.PublishWithId(kvp.Value, kvp.Key);
            }
            order.OutgoingMessages.Clear();
            await orderRepository.Store(order);
        }
    }

    static readonly ILog log = LogManager.GetLogger<AddItemHandler>();
}