using System;
using System.Collections.Generic;
using System.Linq;
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
        Tracer tracer;

        [SetUp]
        public async Task Setup()
        {
            (endpoint, store) = await Program.StartEndpoint(c =>
            {
                c.Pipeline.Register(new TracingBehavior(), "Traces input-output messages");
            });

            tracer = new Tracer();

            await tracer.Start();
        }

        [TearDown]
        public async Task CleanUp()
        {
            await endpoint.Stop();

            await tracer.Stop();
        }

        [Test]
        [TestCaseSource(nameof(TestCases))]
        public async Task PlaceOrder(string caseNo)
        {
            var (conversationId, sendOptions) = tracer.Prepare();

            var message = new PlaceOrder {Id = Guid.NewGuid()};

            await endpoint.Send(message, sendOptions);

            await tracer.WaitUntilFinished(conversationId);

            Assert.That(store.PlacedOrders.Contains(message.Id), "PlaceOrder ");
        }


        static IEnumerable<string> TestCases => Enumerable.Range(1, 25).Select(n => $"{n:00}");
    }
}