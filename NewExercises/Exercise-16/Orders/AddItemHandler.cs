using System;
using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;


class AddItemHandler : IHandleMessages<AddItem>
{
    public async Task Handle(AddItem message,
        IMessageHandlerContext context)
    {
        var order = context.Extensions.Get<Order>();
        var outboxState = context.Extensions.Get<OutboxState>();

        var line = new OrderLine(message.Filling);
        order.Lines.Add(line);
        log.Info($"Item {message.Filling} added.");


        outboxState.OutgoingMessages.Add(new Message(Guid.NewGuid().ToString(), 
            new ItemAdded(message.OrderId, message.Filling)));
        if (order.Lines.Count == 1)
        {
            outboxState.OutgoingMessages.Add(new Message(Guid.NewGuid().ToString(),
                new FirstItemAdded(message.OrderId)));
        }
    }

    static readonly ILog log = LogManager.GetLogger<AddItemHandler>();
}