using System.Threading.Tasks;
using NServiceBus;

static class MessageSessionExtensions
{
    public static Task SendImmediately<T>(this IMessageHandlerContext messageSession, T message) where T : ICommand
    {
        var options = new SendOptions();
        options.RequireImmediateDispatch();
        options.RouteToThisEndpoint();
        return messageSession.Send(message, options);
    }
}