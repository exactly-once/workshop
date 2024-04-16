using System;
using System.Threading.Tasks;
using Microsoft.Extensions.DependencyInjection;
using NServiceBus;

namespace Messaging.IntegrationTests.Tests
{
    public class Tracer
    {
        ConversationTracker conversationTracker;
        IEndpointInstance tracer;

        public async Task Start()
        {
            var configuration = new EndpointConfiguration("trace");
            configuration.UseTransport<LearningTransport>();

            conversationTracker = new ConversationTracker();
            configuration.RegisterComponents(cc => cc.AddSingleton(conversationTracker));

            configuration.AssemblyScanner().ExcludeAssemblies("Marketing.exe", "Orders.exe");

            tracer = await Endpoint.Start(configuration);
        }

        public Task WaitUntilFinished(Guid conversationId, int timeout = 5)
        {
            return Task.WhenAny(
                conversationTracker.WaitForConversationToFinish(conversationId),
                Task.Delay(TimeSpan.FromSeconds(timeout)));
        }

        public (Guid, SendOptions) Prepare()
        {
            var conversationId = Guid.NewGuid();
            var messageId = Guid.NewGuid();
            var sendOptions = new SendOptions();
            sendOptions.StartNewConversation(conversationId.ToString());
            sendOptions.SetMessageId(messageId.ToString());

            conversationTracker.SetupConversationTracking(conversationId, messageId);

            return (conversationId, sendOptions);
        }

        public Task Stop()
        {
            return tracer.Stop();
        }
    }
}