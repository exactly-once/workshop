using NServiceBus;

namespace Messages
{
    public class RemoveItem : IMessage, IOrderMessage
    {
        public string OrderId { get; set; }
        public Filling Filling { get; set; }
    }
}