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
    IDispatchMessages dispatcher;
    IInboxStore inboxStore;

    public OutboxBehavior(OrderRepository orderRepository, IDispatchMessages dispatcher, IInboxStore inboxStore)
    {
        this.orderRepository = orderRepository;
        this.dispatcher = dispatcher;
        this.inboxStore = inboxStore;
    }

    public override async Task Invoke(IIncomingLogicalMessageContext context, Func<Task> next)
    {
        if (!(context.Message.Instance is IOrderMessage orderMessage))
        {
            await next();
            return;
        }

        var order = await orderRepository.Load(orderMessage.OrderId)
                    ?? new Order { Id = orderMessage.OrderId };

        var hasBeenProcessed = await inboxStore.HasBeenProcessed(context.MessageId);
        if (hasBeenProcessed)
        {
            if (order.OutboxState.ContainsKey(context.MessageId))
            {
                order.OutboxState.Remove(context.MessageId);
                await orderRepository.Store(order);
            }

            return; //Duplicate
        }

        if (!order.OutboxState.TryGetValue(context.MessageId, out var outboxState))
        {
            context.Extensions.Set(order);
            var messages = await InvokeMessageHandler(context, next);
            outboxState = new OutboxState { OutgoingMessages = messages.Serialize() };
            order.OutboxState[context.MessageId] = outboxState;
            await orderRepository.Store(order);
        }

        var toDispatch = outboxState.OutgoingMessages.Deserialize();
        await Dispatch(toDispatch, context);

        await inboxStore.MarkProcessed(context.MessageId);

        order.OutboxState.Remove(context.MessageId);
        await orderRepository.Store(order);
    }

    Task Dispatch(TransportOperation[] transportOperations, IExtendable context)
    {
        return dispatcher.Dispatch(new TransportOperations(transportOperations), new TransportTransaction(), context.Extensions);
    }

    static async Task<TransportOperation[]> InvokeMessageHandler(IExtendable context, Func<Task> next)
    {
        var pendingOperations = new PendingTransportOperations();
        context.Extensions.Set(pendingOperations);

        await next();

        return pendingOperations.Operations;
    }
}