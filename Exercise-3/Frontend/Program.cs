using System;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;
using NServiceBus.Serilog;
using Serilog;

class Program
{
    static void Main(string[] args)
    {
        Start().GetAwaiter().GetResult();
    }

    static readonly Regex addExpr = new Regex($"submit ([A-Za-z]+) with ({string.Join("|", Enum.GetNames(typeof(Filling)))})", RegexOptions.IgnoreCase | RegexOptions.Compiled);

    static async Task Start()
    {
        Log.Logger = new LoggerConfiguration()
            .MinimumLevel.Information()
            .WriteTo.Console()
            .CreateLogger();

        LogManager.Use<SerilogFactory>();

        Console.Title = "Frontend";

        var config = new EndpointConfiguration("Frontend");
        config.SendFailedMessagesTo("error");
        var transport = config.UseTransport<LearningTransport>();
        var routing = transport.Routing();
        routing.RouteToEndpoint(typeof(SubmitOrder).Assembly, "Orders");

        config.EnableInstallers();

        var endpoint = await Endpoint.Start(config).ConfigureAwait(false);
        var tokenSource = new CancellationTokenSource();

        var store = new ConsistentInMemoryStore<Order>();
        var importerTask = Task.Run(async () =>
        {
            while (!tokenSource.IsCancellationRequested)
            {
                try
                {
                    await Importer.ImportOrders(store, endpoint);
                }
                catch (Exception e)
                {
                    Console.WriteLine(e.Message);
                }
                await Task.Delay(2000, tokenSource.Token);
            }
        }, tokenSource.Token);

        Console.WriteLine($"'submit <order-id> with ({string.Join("|", Enum.GetNames(typeof(Filling)))})' to add an order with selected filling");

        while (true)
        {
            var command = Console.ReadLine();

            if (string.IsNullOrEmpty(command))
            {
                break;
            }

            var match = addExpr.Match(command);
            if (match.Success)
            {
                var orderId = match.Groups[1].Value;
                var filling = match.Groups[2].Value;

                await store.Put(new Order
                {
                    Filling = (Filling) Enum.Parse(typeof(Filling), filling),
                    Id = orderId
                });

                continue;
            }
            Console.WriteLine("Unrecognized command.");
        }

        tokenSource.Cancel();
        await importerTask.ConfigureAwait(false);
        await endpoint.Stop().ConfigureAwait(false);
    }
}
