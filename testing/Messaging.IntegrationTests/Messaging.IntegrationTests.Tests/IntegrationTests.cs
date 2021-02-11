using System;
using System.Threading.Tasks;
using Messaging.IntegrationTests.System;
using NServiceBus;
using NUnit.Framework;

namespace Messaging.IntegrationTests.Tests
{
    public class IntegrationTests
    {
        IEndpointInstance endpoint;
        OrderStore store;
        
        Tracer tracer = new Tracer();

        [SetUp]
        public async Task Setup()
        {
            (endpoint, store) = await Program.StartEndpoint(c =>
            {
                c.Pipeline.Register(new TracingBehavior(), "Trace input and output messages.");
            });

            await tracer.Start();
        }

        [TearDown]
        public async Task CleanUp()
        {
            await endpoint.Stop();
            await tracer.Stop();
        }

        [Test]
        public async Task PlaceOrder()
        {
            var (conversationId, options) = tracer.Prepare();

            var message = new PlaceOrder {Id = Guid.NewGuid()};

            await endpoint.Send(message, options);

            await tracer.WaitUntilFinished(conversationId);

            Assert.Contains(message.Id, store.PlacedOrders);
        }
    }
}