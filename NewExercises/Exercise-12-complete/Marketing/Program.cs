using System;
using System.Threading.Tasks;
using Microsoft.Azure.Cosmos;
using NServiceBus;
using NServiceBus.Logging;
using NServiceBus.Serilog;
using Serilog;

namespace Marketing
{
    public class Program
    {
        static async Task Main(string[] args)
        {
            var (endpoint, _) = await Start();

            Console.WriteLine("Press <enter> to exit.");
            Console.ReadLine();

            await endpoint.Stop();
        }

        public static async Task<(IEndpointInstance, Repository)> Start(Action<EndpointConfiguration, RoutingSettings> configure = null)
        {
            Log.Logger = new LoggerConfiguration()
                .MinimumLevel.Information()
                .Enrich.With(new ExceptionMessageEnricher())
                .WriteTo.Console(outputTemplate: "[{Timestamp:HH:mm:ss} {Level:u3}] {Message:lj}{ExceptionMessage}{NewLine}")
                .CreateLogger();

            LogManager.Use<SerilogFactory>();

            Console.Title = "Marketing";

            var endpointUri = "https://localhost:8081";
            //TODO: Update key
            var primaryKey = "C2y6yDjf5/R+ob0N8A7Cgv30VRDJIWEHLM+4QDU5DE2nQ9nDuVTqobD4b8mGGyPMbIZnqyMsEcaGQy67XIw/Jw==";
            var cosmosClient = new CosmosClient(endpointUri, primaryKey);

            var repository = new Repository(cosmosClient, "Exercise-11", "Marketing");
            await repository.Initialize();

            var config = new EndpointConfiguration("Marketing");
            var transport = config.UseTransport<LearningTransport>();
            config.RegisterComponents(c =>
            {
                c.RegisterSingleton(repository);
            });
            config.Recoverability().Immediate(x => x.NumberOfRetries(5));
            config.Recoverability().Delayed(x => x.NumberOfRetries(0));
            config.SendFailedMessagesTo("error");
            config.EnableInstallers();
            config.LimitMessageProcessingConcurrencyTo(8);

            configure?.Invoke(config, transport.Routing());

            var endpoint = await Endpoint.Start(config).ConfigureAwait(false);

            return (endpoint, repository);
        }
    }
}
