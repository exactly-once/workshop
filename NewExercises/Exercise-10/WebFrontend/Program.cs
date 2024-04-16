using Microsoft.AspNetCore.Hosting;
using Microsoft.Azure.Cosmos;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;

namespace Orders
{
    using Messages;
    using NServiceBus;
    using WebFrontend;

    public class Program
    {
        public static void Main(string[] args)
        {
            CreateHostBuilder(args).Build().Run();
        }

        public static IHostBuilder CreateHostBuilder(string[] args)
        {
            var clientOptions = new CosmosClientOptions();
            var client = new CosmosClient("AccountEndpoint=https://localhost:8081/;AccountKey=C2y6yDjf5/R+ob0N8A7Cgv30VRDJIWEHLM+4QDU5DE2nQ9nDuVTqobD4b8mGGyPMbIZnqyMsEcaGQy67XIw/Jw==", clientOptions);

            var repository = new Repository(client, "Exercise-10", "WebFrontend");
            repository.Initialize().GetAwaiter().GetResult();


            return Host.CreateDefaultBuilder(args)
                .ConfigureWebHostDefaults(webBuilder => { webBuilder.UseStartup<Startup>(); })
                .UseNServiceBus(context =>
                {
                    var endpointConfiguration = new EndpointConfiguration("WebFrontend");
                    endpointConfiguration.EnableInstallers();
                    var transport = endpointConfiguration.UseTransport<LearningTransport>();
                    transport.Transactions(TransportTransactionMode.ReceiveOnly);
                    var routing = transport.Routing();
                    routing.RouteToEndpoint(typeof(SubmitOrder), "Orders");
                    endpointConfiguration.RegisterComponents(c =>
                    {
                        c.AddSingleton(repository);
                    });
                    endpointConfiguration.Pipeline.Register(new BrokerFailureSimulationBehavior(), "Simulates broker failures");
                    return endpointConfiguration;
                })
                .ConfigureServices(collection =>
                {
                    collection.AddSingleton(sp => new ApplicationServices(repository, sp.GetService<IMessageSession>()));
                });
        }
    }
}
