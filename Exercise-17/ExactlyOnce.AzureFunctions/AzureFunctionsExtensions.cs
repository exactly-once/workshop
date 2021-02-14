using Microsoft.Azure.Cosmos;
using Microsoft.Azure.WebJobs;
using Microsoft.Azure.WebJobs.Description;
using Microsoft.Azure.WebJobs.Host.Bindings;
using Microsoft.Azure.WebJobs.Host.Config;
using Microsoft.Extensions.DependencyInjection;
using System;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace ExactlyOnce.AzureFunctions
{
    [Extension("ExactlyOnce")]
    class ExactlyOnceExtensions : IExtensionConfigProvider
    {
        OnceExecutorFactory factory;

        public ExactlyOnceExtensions(OnceExecutorFactory factory)
        {
            this.factory = factory;
        }

        public void Initialize(ExtensionConfigContext context)
        {
            var rule = context.AddBindingRule<ExactlyOnceAttribute>();

            rule.BindToValueProvider(async (attribute, type) =>
            {
                var requestId = attribute.RequestId;
                var stateId = attribute.StateId ?? attribute.RequestId;

                return new ExactlyOnceValueBinder(requestId, stateId, type, factory);
            });
        }
    }

    public class ExactlyOnceValueBinder : IValueBinder
    {
        string requestId;
        string stateId;
        OnceExecutorFactory factory;

        public ExactlyOnceValueBinder(string requestId, string stateId, Type executorType, OnceExecutorFactory factory)
        {
            this.requestId = requestId;
            this.stateId = stateId;
            this.factory = factory;

            Type = executorType;
        }

        public async Task<object> GetValueAsync()
        {
            if (Type == typeof(IOnceExecutor))
            {
                return factory.Create(requestId);
            }

            var stateType = Type.GetGenericArguments().First();

            var method = typeof(OnceExecutorFactory).GetMethods()
                .First(m => m.IsGenericMethod && m.Name == nameof(OnceExecutorFactory.Create));

            var genericMethod = method.MakeGenericMethod(stateType);

            return genericMethod.Invoke(factory, new object[] { requestId, stateId });
        }

        public string ToInvokeString()
        {
            throw new NotImplementedException();
        }

        public Type Type { get; }

        public Task SetValueAsync(object value, CancellationToken cancellationToken)
        {
            return Task.CompletedTask;
        }
    }

    [Binding]
    [AttributeUsage(AttributeTargets.Parameter)]
    public class ExactlyOnceAttribute : Attribute
    {
        [AutoResolve]
        public string StateId { get; set; }

        [AutoResolve]
        public string RequestId { get; set; }

        public ExactlyOnceAttribute(string requestId, string stateId)
        {
            StateId = stateId;
            RequestId = requestId;
        }

        public ExactlyOnceAttribute(string requestId)
        {
            RequestId = requestId;
        }
    }

    public static class ExactlyOnceHostingExtensions
    {
        public static IWebJobsBuilder AddExactlyOnce(this IWebJobsBuilder builder,
            Action<ExactlyOnceConfiguration> configure)
        {
            builder.AddExtension<ExactlyOnceExtensions>();
            var configuration = builder.Services.RegisterServices();

            configure(configuration);

            configuration.Validate();

            return builder;
        }

        static ExactlyOnceConfiguration RegisterServices(this IServiceCollection services)
        {
            var outboxConfiguration = new OutboxConfiguration();
            var configuration = new ExactlyOnceConfiguration(outboxConfiguration);

            services.AddLogging();

            services.AddSingleton(sp =>
            {
                var client = configuration.CosmosClientFactory();

                var stateStore = new CosmosDbStateStore(client, outboxConfiguration.DatabaseId);

                var outboxStore = new OutboxStore(client, outboxConfiguration);
                return new ExactlyOnceProcessor(outboxStore, stateStore);
            });

            services.AddSingleton<OnceExecutorFactory>();

            return configuration;
        }
    }

    public class ExactlyOnceConfiguration
    {
        OutboxConfiguration outboxConfiguration;

        public Func<CosmosClient> CosmosClientFactory;

        internal ExactlyOnceConfiguration(OutboxConfiguration outboxConfiguration)
        {
            this.outboxConfiguration = outboxConfiguration;
        }

        public ExactlyOnceConfiguration ConfigureOutbox(Action<OutboxConfiguration> configure)
        {
            configure(outboxConfiguration);

            outboxConfiguration.Validate();

            return this;
        }

        public void UseCosmosClient(Func<CosmosClient> factory)
        {
            CosmosClientFactory = factory;
        }

        public void Validate()
        {
            if (CosmosClientFactory == default)
            {
                throw new Exception($"CosmosClient must be configured via {nameof(UseCosmosClient)} method." );
            }
        }
    }
}