using System.Threading.Tasks;
using NServiceBus;

static class MessageSessionExtensions
{
    public static Task PublishImmediately<T>(this IMessageHandlerContext messageSession, T message) where T : IEvent
    {
        var options = new PublishOptions();
        options.RequireImmediateDispatch();
        return messageSession.Publish(message, options);
    }
}