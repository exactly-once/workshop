using System.Linq;
using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;

class SubmitOrderHandler : IHandleMessages<SubmitOrder>
{
    public Task Handle(SubmitOrder message, IMessageHandlerContext context)
    {
        var order = context.Extensions.Get<Order>();
        order.Lines = message.Items.Select(x => new OrderLine(x)).ToList();

        log.Info($"Order {message.OrderId} created.");

        return Task.CompletedTask;
    }

    static readonly ILog log = LogManager.GetLogger<SubmitOrderHandler>();
}