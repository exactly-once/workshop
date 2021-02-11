using NServiceBus;

namespace Messages
{
    public class AddItem : IMessage, IOrderMessage
    {
        public string OrderId { get; set; }
        public Filling Filling { get; set; }
    }
}