using System;
using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Extensibility;
using NServiceBus.Pipeline;
using NServiceBus.Transport;

class OutboxBehavior : Behavior<IIncomingLogicalMessageContext>
{
    OrderRepository orderRepository;

    public OutboxBehavior(OrderRepository orderRepository)
    {
        this.orderRepository = orderRepository;
    }

    public override async Task Invoke(IIncomingLogicalMessageContext context, Func<Task> next)
    {
        if (!(context.Message.Instance is IOrderMessage orderMessage))
        {
            await next();
            return;
        }

        //TODO: Outbox logic

        //var outgoingMessages = await InvokeMessageHandler(context, next);
    }

    static async Task<TransportOperation[]> InvokeMessageHandler(IExtendable context, Func<Task> next)
    {
        var pendingOperations = new PendingTransportOperations();
        context.Extensions.Set(pendingOperations);

        await next();

        return pendingOperations.Operations;
    }
}