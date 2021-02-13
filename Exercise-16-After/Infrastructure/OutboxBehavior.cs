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

        if (entity.TransactionId != null)
        {
            outboxState = await outboxStore.Get(entity.TransactionId);
            version = await FinishTransaction(context, outboxState, entity, version);
        }

        var hasBeenProcessed = await inboxStore.HasBeenProcessed(context.MessageId);
        if (hasBeenProcessed)
        {
            return;
        }

        var transactionId = Guid.NewGuid().ToString();
        context.Extensions.Set(entity);
        var messages = await InvokeMessageHandler(context, next);
        outboxState = new OutboxState { OutgoingMessages = messages.Serialize() };

        await outboxStore.Put(transactionId, outboxState);

        entity.TransactionId = transactionId;
        version = await repository.Put(entity, version);

        await FinishTransaction(context, outboxState, entity, version);
    }

    async Task<string> FinishTransaction(IMessageProcessingContext context, OutboxState outboxState, T entity, string version)
    {
        if (outboxState != null)
        {
            var toDispatch = outboxState.OutgoingMessages.Deserialize();
            await Dispatch(toDispatch, context);
            await outboxStore.Delete(entity.TransactionId);
        }

        await inboxStore.MarkProcessed(context.MessageId);

        entity.TransactionId = null;
        return await repository.Put(entity, version);
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