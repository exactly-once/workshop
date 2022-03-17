using System;
using System.Linq;
using System.Threading.Tasks;
using NServiceBus;
using NServiceBus.Pipeline;

namespace Messaging.IntegrationTests.Tests
{
    public class TracingBehavior : Behavior<IIncomingLogicalMessageContext>
    {
        public override async Task Invoke(IIncomingLogicalMessageContext context, Func<Task> next)
        {
            await next().ConfigureAwait(false);

            var pending = context.Extensions.Get<PendingTransportOperations>();

            var trace = new TraceMessage
            {
                ConversationId = Guid.Parse(context.Headers[Headers.ConversationId]),
                IncomingMessageId = Guid.Parse(context.Headers[Headers.MessageId]),
                OutgoingMessageId = pending.Operations.Select(o => Guid.Parse((string) o.Message.Headers[Headers.MessageId]))
                    .ToArray()
            };

            var sendOptions = new SendOptions();
            sendOptions.SetDestination("trace");

            await context.Send(trace, sendOptions);
        }
    }
}