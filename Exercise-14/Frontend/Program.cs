using System;
using System.Text.RegularExpressions;
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

    static readonly Regex submitExpr = new Regex("submit ([A-Za-z]+)", RegexOptions.IgnoreCase | RegexOptions.Compiled);
    static readonly Regex createExpr = new Regex("create ([A-Za-z]+)", RegexOptions.IgnoreCase | RegexOptions.Compiled);
    static readonly Regex addExpr = new Regex($"add ({string.Join("|", Enum.GetNames(typeof(Filling)))}) to ([A-Za-z]+)", RegexOptions.IgnoreCase | RegexOptions.Compiled);
    static readonly Regex removeExpr = new Regex($"remove ({string.Join("|", Enum.GetNames(typeof(Filling)))}) from ([A-Za-z]+)", RegexOptions.IgnoreCase | RegexOptions.Compiled);

    static async Task Start()
    {
        Log.Logger = new LoggerConfiguration()
            .MinimumLevel.Information()
            .WriteTo.Console()
            .CreateLogger();

        LogManager.Use<SerilogFactory>();

        Console.Title = "Frontend";

        var endpointUri = "https://localhost:8081";
        //TODO: Update key
        var primaryKey = "C2y6yDjf5/R+ob0N8A7Cgv30VRDJIWEHLM+4QDU5DE2nQ9nDuVTqobD4b8mGGyPMbIZnqyMsEcaGQy67XIw/Jw==";
        var cosmosClient = new CosmosClient(endpointUri, primaryKey);

        var repository = new ShoppingCartRepository(cosmosClient, "Ex14");
        var inbox = new TokenStore(cosmosClient, "Ex14");

        await repository.Initialize();
        await inbox.Initialize();

        var config = new EndpointConfiguration("Frontend");
        config.Pipeline.Register(new DuplicateMessagesBehavior(), "Duplicates outgoing messages");
        config.SendFailedMessagesTo("error");
        var routing = config.UseTransport<LearningTransport>().Routing();
        routing.RouteToEndpoint(typeof(SubmitOrder).Assembly, "Orders");
        config.Pipeline.Register(b => new OutboxBehavior<ShoppingCart>(repository, b.Build<IDispatchMessages>(), inbox,
            m =>
            {
                if (m is SendSubmitOrder sendSubmit)
                {
                    return sendSubmit.OrderId;
                }

                return null;
            }), "Deduplicates incoming messages");


        config.EnableInstallers();

        var endpoint = await Endpoint.Start(config).ConfigureAwait(false);
        var appServices = new ApplicationServices(repository, endpoint);

        Console.WriteLine("'create <order-id>' to create a new order.");
        Console.WriteLine("'submit <order-id>' to submit an order.");
        Console.WriteLine($"'add ({string.Join("|", Enum.GetNames(typeof(Filling)))}) to <order-id>' to add item with selected filling.");

        while (true)
        {
            var command = Console.ReadLine();

            if (string.IsNullOrEmpty(command))
            {
                break;
            }

            var match = submitExpr.Match(command);
            if (match.Success)
            {
                var orderId = match.Groups[1].Value;
                await appServices.SubmitOrder(orderId);
                continue;
            }
            match = createExpr.Match(command);
            if (match.Success)
            {
                var orderId = match.Groups[1].Value;
                await appServices.CreateOrder(orderId);
                continue;
            }
            match = addExpr.Match(command);
            if (match.Success)
            {
                var filling = match.Groups[1].Value;
                var orderId = match.Groups[2].Value;

                await appServices.AddItem(orderId, (Filling)Enum.Parse(typeof(Filling), filling));
                continue;
            }
            match = removeExpr.Match(command);
            if (match.Success)
            {
                var filling = match.Groups[1].Value;
                var orderId = match.Groups[2].Value;
                await appServices.RemoveItem(orderId, (Filling)Enum.Parse(typeof(Filling), filling));
                continue;
            }
            Console.WriteLine("Unrecognized command.");
        }

        await endpoint.Stop().ConfigureAwait(false);
    }
}
