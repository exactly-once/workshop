using NServiceBus;

namespace Messages
{
    public class ItemAdded : IEvent
    {
        public ItemAdded()
        {
        }

        public ItemAdded(string orderId, Filling filling)
        {
            OrderId = orderId;
            Filling = filling;
        }

        public string OrderId { get; set; }
        public Filling Filling { get; set; }
    }
}