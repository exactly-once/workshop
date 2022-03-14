using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;

class SubmitOrderHandler : IHandleMessages<SubmitOrder>
{
    Repository repository;

    public SubmitOrderHandler(Repository repository)
    {
        this.repository = repository;
    }

    public Task Handle(SubmitOrder message, IMessageHandlerContext context)
    {
        return Task.CompletedTask;
    }

    static readonly ILog log = LogManager.GetLogger<SubmitOrderHandler>();
}