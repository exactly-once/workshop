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
            (endpoint, store) = await Program.StartEndpoint();
        }

        [Test]
        public async Task PlaceOrder()
        {
            var id = Guid.NewGuid();
            await endpoint.Send(new PlaceOrder{Id = id});

            Assert.Contains(id, store.PlacedOrders);
        }
    }
}
