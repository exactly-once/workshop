using System.Threading.Tasks;
using NServiceBus;

static class MessageSessionExtensions
{
    public static Task PublishWithId(this IPipelineContext messageSession, object message, string id)
    {
        var options = new PublishOptions();
        options.SetMessageId(id);
        options.RequireImmediateDispatch();
        return messageSession.Publish(message, options);
    }
}