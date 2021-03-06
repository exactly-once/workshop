﻿using System;
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
    readonly ITokenStore tokenStore;
    readonly Func<object, string> getId;

    public OutboxBehavior(Repository<T> repository, IDispatchMessages dispatcher, ITokenStore tokenStore, Func<object, string> getId)
    {
        this.repository = repository;
        this.dispatcher = dispatcher;
        this.tokenStore = tokenStore;
        this.getId = getId;
    }

    public override async Task Invoke(IIncomingLogicalMessageContext context, Func<Task> next)
    {
        var id = getId(context.Message.Instance);
        if (id == null)
        {
            await next();
            return;
        }

        var (entity, version) = await repository.Get(id);

        var hasBeenProcessed = await tokenStore.HasBeenProcessed(context.MessageId);
        if (hasBeenProcessed)
        {
            if (entity.OutboxState.ContainsKey(context.MessageId))
            {
                entity.OutboxState.Remove(context.MessageId);
                await repository.Put(entity, version);
            }
            return; //Duplicate
        }

        if (!entity.OutboxState.TryGetValue(context.MessageId, out var outboxState))
        {
            context.Extensions.Set(entity);
            var messages = await InvokeMessageHandler(context, next);
            outboxState = new OutboxState { OutgoingMessages = messages.Serialize() };
            entity.OutboxState[context.MessageId] = outboxState;

            version = await repository.Put(entity, version);
        }

        var toDispatch = outboxState.OutgoingMessages.Deserialize();
        await Dispatch(toDispatch, context);

        await tokenStore.MarkProcessed(context.MessageId);

        entity.OutboxState.Remove(context.MessageId);
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