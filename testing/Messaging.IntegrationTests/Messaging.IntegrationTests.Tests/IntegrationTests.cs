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

        [SetUp]
        public async Task Setup()
        {
            (endpoint, store) = await Program.StartEndpoint(c =>
            {
                /*TODO: register tracing behavior */
            });

            /*TODO: create tracer instance and start it*/
        }

        [TearDown]
        public async Task CleanUp()
        {
            await endpoint.Stop();

            /*TODO: stop the tracer */
        }

        [Test]
        [TestCaseSource(nameof(TestCases))]
        public async Task PlaceOrder(string caseNo)
        {
            var message = new PlaceOrder {Id = Guid.NewGuid()};

            await endpoint.Send(message);

            Assert.That(store.PlacedOrders.Contains(message.Id), "PlaceOrder ");
        }


        static IEnumerable<string> TestCases => Enumerable.Range(1, 25).Select(n => $"{n:00}");
    }
}