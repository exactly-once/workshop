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

            var outgoingMessages = context.Extensions.Get<PendingTransportOperations>();

            var trace = new TraceMessage
            {
                ConversationId = Guid.Parse(context.Headers[Headers.ConversationId]),
                IncomingMessageId = Guid.Parse(context.Headers[Headers.MessageId])
                /*TODO: add missing code here */
            };

            var sendOptions = new SendOptions();
            sendOptions.SetDestination("trace");

            await context.Send(trace, sendOptions);
        }
    }
}