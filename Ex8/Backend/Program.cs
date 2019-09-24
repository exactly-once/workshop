using System;
using System.Data.Entity.Validation;
using System.Data.SqlClient;
using System.Linq;
using System.Reflection.Emit;
using System.Threading.Tasks;
using NServiceBus;
using NServiceBus.Logging;
using NServiceBus.Serilog;
using Serilog;
using Serilog.Filters;

class Program
{
    public const string ConnectionString = @"Data Source=(local);Database=Workshop.ExactlyOnce;Integrated Security=True";

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

        var config = new EndpointConfiguration("ExactlyOnce.Orders");
        config.UseTransport<LearningTransport>();
        config.Recoverability().Immediate(x => x.NumberOfRetries(5));
        config.Recoverability().Delayed(x => x.NumberOfRetries(0));
        config.Recoverability().AddUnrecoverableException(typeof(DbEntityValidationException));
        config.Pipeline.Register(new BrokerFailureBehavior(), "Simulates broker failures");
        config.Pipeline.Register(new BrokerFailureDispatchBehavior(), "Simulates broker failures");
        config.Pipeline.Register(new DeduplicatingBehavior(), "Deduplicates incoming messages");
        config.SendFailedMessagesTo("error");
        config.EnableInstallers();
        config.LimitMessageProcessingConcurrencyTo(10);

        SqlHelper.EnsureDatabaseExists(ConnectionString);

        using (var receiverDataContext = new OrdersDataContext(new SqlConnection(ConnectionString)))
        {
            receiverDataContext.Database.Initialize(true);
        }

        var endpoint = await Endpoint.Start(config).ConfigureAwait(false);

        Console.WriteLine("Press <enter> to exit.");
        Console.ReadLine();

        await endpoint.Stop().ConfigureAwait(false);
    }
}