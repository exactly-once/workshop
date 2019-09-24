using System;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;
using NServiceBus.Serilog;
using Serilog;
using Serilog.Filters;

class Program
{
    static void Main(string[] args)
    {
        Start().GetAwaiter().GetResult();
    }

    static readonly Regex submitExpr = new Regex("submit ([A-Za-z]+)", RegexOptions.IgnoreCase | RegexOptions.Compiled);
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

        var config = new EndpointConfiguration("ExactlyOnce.Frontend");
        config.SendFailedMessagesTo("error");
        config.Pipeline.Register(new DuplicateMessagesBehavior(), "Duplicates outgoing messages");
        var routing = config.UseTransport<LearningTransport>().Routing();
        routing.RouteToEndpoint(typeof(SubmitOrder).Assembly, "ExactlyOnce.Orders");

        config.EnableInstallers();

        var endpoint = await Endpoint.Start(config).ConfigureAwait(false);

        Console.WriteLine("'submit <order-id>' to create a new order.");
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
                var message = new SubmitOrder
                {
                    OrderId = orderId
                };
                Task.Run(() => endpoint.Send(message));
                continue;
            }
            match = addExpr.Match(command);
            if (match.Success)
            {
                var filling = match.Groups[1].Value;
                var orderId = match.Groups[2].Value;
                var message = new AddItem
                {
                    OrderId = orderId,
                    Filling = (Filling)Enum.Parse(typeof(Filling), filling)
                };
                var options = new SendOptions();
                Task.Run(() => endpoint.Send(message, options));
                continue;
            }
            match = removeExpr.Match(command);
            if (match.Success)
            {
                var filling = match.Groups[1].Value;
                var orderId = match.Groups[2].Value;
                var message = new RemoveItem
                {
                    OrderId = orderId,
                    Filling = (Filling)Enum.Parse(typeof(Filling), filling)
                };
                var options = new SendOptions();
                Task.Run(() => endpoint.Send(message, options));
                continue;
            }
            Console.WriteLine("Unrecognized command.");
        }

        await endpoint.Stop().ConfigureAwait(false);
    }
}
