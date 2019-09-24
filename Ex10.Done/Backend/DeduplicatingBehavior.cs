using System;
using System.Collections.Generic;
using System.Data.Entity;
using System.Threading.Tasks;
using Newtonsoft.Json;
using NServiceBus;
using NServiceBus.Pipeline;

class DeduplicatingBehavior : Behavior<IIncomingLogicalMessageContext>
{
    static JsonSerializerSettings serializerSettings = new JsonSerializerSettings()
    {
        TypeNameHandling = TypeNameHandling.Auto
    };

    public override async Task Invoke(IIncomingLogicalMessageContext context, Func<Task> next)
    {
        var dbContext = new OrdersDataContext();
        ProcessedMessage processedMessage;

        using (var dbContextTransaction = dbContext
            .Database.BeginTransaction())
        {
            processedMessage = await dbContext
                .ProcessedMessages
                .FirstOrDefaultAsync(m => m.MessageId == context.MessageId);

            if (processedMessage == null)
            {
                processedMessage = new ProcessedMessage {MessageId = context.MessageId};
                dbContext.ProcessedMessages.Add(processedMessage);

                await dbContext.SaveChangesAsync()
                    .ConfigureAwait(false);

                context.Extensions.Set(dbContext);

                await next().ConfigureAwait(false); //Process

                var serializedMessages = JsonConvert.SerializeObject(dbContext.OutgoingMessages, serializerSettings);
                processedMessage.OutgoingMessages = serializedMessages;

                await dbContext.SaveChangesAsync()
                    .ConfigureAwait(false);
            }

            dbContextTransaction.Commit();
        }

        var outgoingMessages =
            JsonConvert.DeserializeObject<List<OutgoingMessage>>(processedMessage.OutgoingMessages, serializerSettings);

        foreach (var outgoingMessage in outgoingMessages)
        {
            var publishOptions = new PublishOptions();
            publishOptions.SetMessageId(outgoingMessage.MessageId);
            await context.Publish(outgoingMessage.Payload, publishOptions);
        }
    }
}