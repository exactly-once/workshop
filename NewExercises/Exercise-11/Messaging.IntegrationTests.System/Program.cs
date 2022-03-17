using System;
using System.Collections.Generic;
using System.Threading.Tasks;
using NServiceBus;

namespace Messaging.IntegrationTests.System
{
    public class Program
    {
        static async Task Main(string[] args)
        {
            await StartEndpoint();

            Console.WriteLine("Press any <key> to exit.");
            Console.ReadKey();
        }

        public static async Task<(IEndpointInstance, OrderStore)> StartEndpoint(Action<EndpointConfiguration> configure = null)
        {
            var endpointName = "IntegrationTests.Endpoint";
            
            var configuration = new EndpointConfiguration(endpointName);
            
            var transport = configuration.UseTransport<LearningTransport>();
            transport.Routing().RouteToEndpoint(typeof(PlaceOrder), endpointName);

            var orderStore = new OrderStore();
            configuration.RegisterComponents(cc => cc.RegisterSingleton(orderStore));

            configure?.Invoke(configuration);

            var endpoint = await Endpoint.Start(configuration).ConfigureAwait(false);

            return (endpoint, orderStore);
        }
    }

    public class PlaceOrder : ICommand
    {
        public Guid Id { get; set; }
    }

    public class FinalizeOrder : ICommand
    {
        public Guid Id { get; set; }
    }

    public class OrderStore
    {
        public List<Guid> PlacedOrders = new List<Guid>();
    }

    public class PlaceOrderHandler : IHandleMessages<PlaceOrder>,
        IHandleMessages<FinalizeOrder>
    {
        readonly OrderStore store;

        public PlaceOrderHandler(OrderStore store)
        {
            this.store = store;
        }

        public async Task Handle(PlaceOrder message, IMessageHandlerContext context)
        {
            Console.WriteLine("Order received");

            if (new Random().Next(0, 20) == 0)
            {
                Console.WriteLine("Delaying order processing");

                var options = new SendOptions();
                options.DelayDeliveryWith(TimeSpan.FromSeconds(10));

                await context.Send(message, options);
            }
            else
            {
                await context.SendLocal(new FinalizeOrder{Id = message.Id});
            }
        }

        public Task Handle(FinalizeOrder message, IMessageHandlerContext context)
        {
            Console.WriteLine("Finalizing order");

            store.PlacedOrders.Add(message.Id);

            return Task.CompletedTask;
        }
    }
}
