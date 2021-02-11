using NServiceBus;

namespace Messages
{
    public class SubmitOrder : IMessage
    {
        public string OrderId { get; set; }
    }
}
