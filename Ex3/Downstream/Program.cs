using System;
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

    static async Task Start()
    {
        Log.Logger = new LoggerConfiguration()
            .MinimumLevel.Information()
            .Filter.ByExcluding(Matching.FromSource("NServiceBus.Transport.Msmq.QueuePermissions"))
            .WriteTo.Console()
            .CreateLogger();

        LogManager.Use<SerilogFactory>();

        Console.Title = "Billing";

        var config = new EndpointConfiguration("OnlyOnce.Demo0.Billing");
        config.UsePersistence<InMemoryPersistence>();
        var transport = config.UseTransport<MsmqTransport>();
        transport.Transactions(TransportTransactionMode.ReceiveOnly);
        transport.Routing().RegisterPublisher(typeof(ItemAdded), "OnlyOnce.Demo0.Orders");
        config.Recoverability().Immediate(x => x.NumberOfRetries(5));
        config.Recoverability().Delayed(x => x.NumberOfRetries(0));
        config.SendFailedMessagesTo("error");
        config.EnableInstallers();

        var endpoint = await Endpoint.Start(config).ConfigureAwait(false);

        while (true)
        {
            Console.WriteLine("Press <enter> to exit.");
            Console.ReadLine();
        }
    }
}
