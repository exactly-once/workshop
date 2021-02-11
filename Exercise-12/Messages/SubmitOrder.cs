using NServiceBus;

namespace Messages
{
    public class SubmitOrder : IMessage, IOrderMessage
    {
        public string OrderId { get; set; }
    }
}
