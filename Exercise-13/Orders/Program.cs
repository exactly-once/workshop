using System;
using System.Threading.Tasks;
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

        var config = new EndpointConfiguration("OnlyOnce.Demo0.Orders");
        config.UseTransport<LearningTransport>();
        config.Pipeline.Register(new BrokerErrorSimulatorBehavior(), "Simulates broker errors");
        config.Pipeline.Register(b => new OutboxBehavior(b.Build<OrderRepository>(), b.Build<IDispatchMessages>()),
            "Deduplicates incoming messages");
        var orderRepository = new OrderRepository();
        config.RegisterComponents(c =>
        {
            c.RegisterSingleton(orderRepository);
        });
        config.Recoverability().Immediate(x => x.NumberOfRetries(5));
        config.Recoverability().Delayed(x => x.NumberOfRetries(0));
        config.Recoverability().AddUnrecoverableException<DatabaseErrorException>();
        config.SendFailedMessagesTo("error");
        config.EnableInstallers();
        config.LimitMessageProcessingConcurrencyTo(8);

        var endpoint = await Endpoint.Start(config).ConfigureAwait(false);

        while (true)
        {
            Console.WriteLine("Press <enter> to dump database.");
            Console.ReadLine();
            orderRepository.Dump(Console.Out);
        }
    }
}