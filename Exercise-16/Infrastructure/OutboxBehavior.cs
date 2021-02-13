using System;
using System.Threading.Tasks;
using NServiceBus;
using NServiceBus.Extensibility;
using NServiceBus.Pipeline;
using NServiceBus.Transport;

public class OutboxBehavior<T> : Behavior<IIncomingLogicalMessageContext>
    where T : Entity, new()
{
    readonly Repository<T> repository;
    readonly IDispatchMessages dispatcher;
    readonly IInboxStore inboxStore;
    readonly IOutboxStore outboxStore;
    readonly Func<object, string> getId;

    public OutboxBehavior(Repository<T> repository, IDispatchMessages dispatcher, IInboxStore inboxStore,
        IOutboxStore outboxStore, Func<object, string> getId)
    {
        this.repository = repository;
        this.dispatcher = dispatcher;
        this.inboxStore = inboxStore;
        this.getId = getId;
        this.outboxStore = outboxStore;
    }

    public override async Task Invoke(IIncomingLogicalMessageContext context, Func<Task> next)
    {
        var id = getId(context.Message.Instance);
        if (id == null)
        {
            await next();
            return;
        }

        OutboxState outboxState;

        var (entity, version) = await repository.Get(id);

        var hasBeenProcessed = await inboxStore.HasBeenProcessed(context.MessageId);
        if (hasBeenProcessed)
        {
            if (entity.TransactionIds.ContainsKey(context.MessageId))
            {
                entity.TransactionIds.Remove(context.MessageId);
                await repository.Put(entity, version);
            }
            return;
        }

        if (!entity.TransactionIds.TryGetValue(context.MessageId, out var transactionId))
        {
            transactionId = Guid.NewGuid().ToString();

            context.Extensions.Set(entity);
            var messages = await InvokeMessageHandler(context, next);
            outboxState = new OutboxState { OutgoingMessages = messages.Serialize() };

            await outboxStore.Put(transactionId, outboxState);

            entity.TransactionIds[context.MessageId] = transactionId;
            version = await repository.Put(entity, version);
        }
        else
        {
            outboxState = await outboxStore.Get(transactionId);
        }

        if (outboxState != null)
        {
            var toDispatch = outboxState.OutgoingMessages.Deserialize();
            await Dispatch(toDispatch, context);
            await outboxStore.Delete(transactionId);
        }

        await inboxStore.MarkProcessed(context.MessageId);

        entity.TransactionIds.Remove(context.MessageId);
        await repository.Put(entity, version);
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