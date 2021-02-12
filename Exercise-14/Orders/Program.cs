using System;
using System.Threading.Tasks;
using Messages;
using Microsoft.Azure.Cosmos;
using NServiceBus;
using NServiceBus.Logging;
using NServiceBus.Serilog;
using NServiceBus.Transport;
using Serilog;

class Program
{
    static void Main(string[] args)
    {
        Start().GetAwaiter().GetResult();
    }

    static async Task Start()
    {
        Log.Logger = new LoggerConfiguration()
            .MinimumLevel.Information()
            .Enrich.With(new ExceptionMessageEnricher())
            .WriteTo.Console(outputTemplate: "[{Timestamp:HH:mm:ss} {Level:u3}] {Message:lj}{ExceptionMessage}{NewLine}")
            .CreateLogger();

        LogManager.Use<SerilogFactory>();

        Console.Title = "Orders";

        var endpointUri = "https://localhost:8081";
        //TODO: Update key
        var primaryKey = "C2y6yDjf5/R+ob0N8A7Cgv30VRDJIWEHLM+4QDU5DE2nQ9nDuVTqobD4b8mGGyPMbIZnqyMsEcaGQy67XIw/Jw==";
        var cosmosClient = new CosmosClient(endpointUri, primaryKey);

        var repository = new OrderRepository(cosmosClient, "Ex14");
        var inbox = new InboxStore(cosmosClient, "Ex14");

        await repository.Initialize();
        await inbox.Initialize();


        var config = new EndpointConfiguration("Orders");
        config.UseTransport<LearningTransport>();
        config.Pipeline.Register(b => new OutboxBehavior<Order>(repository, b.Build<IDispatchMessages>(), inbox,
                m =>
                {
                    if (m is SubmitOrder submit)
                    {
                        return submit.OrderId;
                    }

                    return null;
                }),
            "Deduplicates incoming messages");

        config.Recoverability().Immediate(x => x.NumberOfRetries(5));
        config.Recoverability().Delayed(x => x.NumberOfRetries(0));
        config.SendFailedMessagesTo("error");
        config.EnableInstallers();
        config.LimitMessageProcessingConcurrencyTo(8);

        var endpoint = await Endpoint.Start(config).ConfigureAwait(false);

        Console.WriteLine("Press <enter> to exit.");
        Console.ReadLine();

        await endpoint.Stop();
    }
}