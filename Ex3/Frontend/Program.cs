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

    static async Task Start()
    {
        Log.Logger = new LoggerConfiguration()
            .MinimumLevel.Information()
            .Filter.ByExcluding(Matching.FromSource("NServiceBus.Transport.Msmq.QueuePermissions"))
            .WriteTo.Console()
            .CreateLogger();

        LogManager.Use<SerilogFactory>();

        Console.Title = "Frontend";

        var config = new EndpointConfiguration("ExactlyOnce.Ex1.Frontend");
        config.SendFailedMessagesTo("error");
        config.Pipeline.Register(new DuplicateMessagesBehavior(), "Duplicates outgoing messages");
        var routing = config.UseTransport<LearningTransport>().Routing();
        routing.RouteToEndpoint(typeof(SubmitOrder).Assembly, "ExactlyOnce.Ex1.Orders");

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
                await endpoint.Send(message).ConfigureAwait(false);
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
                await endpoint.Send(message, options).ConfigureAwait(false);
                continue;
            }
            Console.WriteLine("Unrecognized command.");
        }

        await endpoint.Stop().ConfigureAwait(false);
    }
}
