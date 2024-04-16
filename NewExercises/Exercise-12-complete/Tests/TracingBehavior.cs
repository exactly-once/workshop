using System;
using System.Collections.Generic;
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
            var immediateMessages = new List<Guid>();

            context.Extensions.Set(ImmediateDispatchIds, immediateMessages);

            await next().ConfigureAwait(false);

            var pending = context.Extensions.Get<PendingTransportOperations>();
            
            var trace = new TraceMessage
            {
                ConversationId = Guid.Parse(context.Headers[Headers.ConversationId]),
                IncomingMessageId = Guid.Parse(context.Headers[Headers.MessageId]),
                OutgoingMessageId = pending.Operations
                    .Select(o => Guid.Parse((string) o.Message.Headers[Headers.MessageId]))
                    .Union(immediateMessages)
                    .ToArray()
            };

            var sendOptions = new SendOptions();
            sendOptions.SetDestination("trace");

            await context.Send(trace, sendOptions);
        }

        public const string ImmediateDispatchIds = "Tracking.ImmediateDispatchIds";
    }

    public class ImmediateTracingBehavior : Behavior<IOutgoingPhysicalMessageContext>
    {
        public override Task Invoke(IOutgoingPhysicalMessageContext context, Func<Task> next)
        {
            if(context.Extensions.TryGet<List<Guid>>(TracingBehavior.ImmediateDispatchIds, out var immediateDispatchIds))
            {
                if (context.Headers[Headers.EnclosedMessageTypes].Contains(nameof(TraceMessage)) == false)
                {
                    immediateDispatchIds.Add(Guid.Parse(context.Headers[Headers.MessageId]));
                }
            }

            return next();
        }
    }
}