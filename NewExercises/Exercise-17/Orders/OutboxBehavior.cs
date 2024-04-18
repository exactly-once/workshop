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

        if (!order.OutgoingMessages.ContainsKey(context.MessageId))
        {
            var outboxState = new OutboxState();
            order.OutgoingMessages.Add(context.MessageId, outboxState);
            context.Extensions.Set(outboxState);

            await next();
            await orderRepository.Store(order);
        }

        if (order.OutgoingMessages[context.MessageId] != null)
        {
            foreach (var kvp in order.OutgoingMessages[context.MessageId].OutgoingMessages)
            {
                await context.PublishWithId(kvp.Payload, kvp.Id);
            }

            order.OutgoingMessages[context.MessageId] = null;
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