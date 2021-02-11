using System.Threading.Tasks;
using Messages;
using NServiceBus;
using NServiceBus.Logging;

public class FirstItemAddedHandler : IHandleMessages<FirstItemAdded>
{
    public Task Handle(FirstItemAdded message, IMessageHandlerContext context)
    {
        log.Info($"Message {context.MessageId}: First item added to order {message.OrderId}");
        return Task.FromResult(0);
    }

    static readonly ILog log = LogManager.GetLogger<FirstItemAddedHandler>();
}