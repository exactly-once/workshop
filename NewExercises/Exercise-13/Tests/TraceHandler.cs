using System.Threading.Tasks;
using NServiceBus;

namespace Messaging.IntegrationTests.Tests
{
    public class TraceHandler : IHandleMessages<TraceMessage>
    {
        readonly ConversationTracker tracker;

        public TraceHandler(ConversationTracker tracker)
        {
            this.tracker = tracker;
        }

        public Task Handle(TraceMessage message, IMessageHandlerContext context)
        {
            tracker.UpdateConversations(message);

            return Task.CompletedTask;
        }
    }
}