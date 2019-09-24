using System;
using System.Data.Entity;
using System.Threading.Tasks;
using NServiceBus.Pipeline;

class DeduplicatingBehavior : Behavior<IIncomingLogicalMessageContext>
{
    public override async Task Invoke(IIncomingLogicalMessageContext context, Func<Task> next)
    {
        var dbContext = new OrdersDataContext();

        using (var dbContextTransaction = dbContext
            .Database.BeginTransaction())
        {
            var processedMessage = await dbContext
                .ProcessedMessages
                .FirstOrDefaultAsync(m => m.MessageId == context.MessageId);

            if (processedMessage != null)
            {
                dbContext.Processed = true;
            }
            else
            {
                dbContext.ProcessedMessages.Add(new ProcessedMessage {MessageId = context.MessageId});
            }

            await dbContext.SaveChangesAsync()
                .ConfigureAwait(false);

            context.Extensions.Set(dbContext);

            await next().ConfigureAwait(false); //Process

            await dbContext.SaveChangesAsync()
                .ConfigureAwait(false);

            dbContextTransaction.Commit();
        }
    }
}