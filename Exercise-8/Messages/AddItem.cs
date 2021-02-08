using NServiceBus;

namespace Messages
{
    public class AddItem : IMessage
    {
        public string OrderId { get; set; }
        public Filling Filling { get; set; }
    }
}