using System;
using System.Linq;
using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Extensibility;
using NServiceBus.Pipeline;
using NServiceBus.Transport;

class OutboxBehavior : Behavior<IIncomingLogicalMessageContext>
{
    OrderRepository orderRepository;
    IMessageDispatcher dispatcher;

    public OutboxBehavior(OrderRepository orderRepository, IMessageDispatcher dispatcher)
    {
        this.orderRepository = orderRepository;
        this.dispatcher = dispatcher;
    }

    public override async Task Invoke(IIncomingLogicalMessageContext context, Func<Task> next)
    {
        if (!(context.Message.Instance is IOrderMessage orderMessage))
        {
            await next();
            return;
        }

        var order = await orderRepository.Load(orderMessage.OrderId);
        context.Extensions.Set(order);

        if (!order.ProcessedMessages.Contains(context.MessageId))
        {

            await next();
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

    Task Dispatch(TransportOperation[] transportOperations, IExtendable context)
    {
        return dispatcher.Dispatch(new TransportOperations(transportOperations), new TransportTransaction());
    }

    static async Task<TransportOperation[]> InvokeMessageHandler(IExtendable context, Func<Task> next)
    {
        var pendingOperations = new PendingTransportOperations();
        context.Extensions.Set(pendingOperations);

        await next();

        return pendingOperations.Operations;
    }
}