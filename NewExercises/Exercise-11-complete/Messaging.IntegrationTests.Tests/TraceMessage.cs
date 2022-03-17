using System;
using NServiceBus;

namespace Messaging.IntegrationTests.Tests
{
    public class TraceMessage : IMessage
    {
        public Guid ConversationId { get; set; }
        public Guid IncomingMessageId { get; set; }
        public Guid[] OutgoingMessageId { get; set; }
    }
}