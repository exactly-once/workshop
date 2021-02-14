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
        [Repeat(25)]
        public async Task PlaceOrder()
        {
            var message = new PlaceOrder {Id = Guid.NewGuid()};

            await endpoint.Send(message);

            Assert.Contains(message.Id, store.PlacedOrders, "PlaceOrder ");
        }
    }
}