using NServiceBus;

namespace Messages
{
    public class ItemRemoved : IEvent
    {
        public ItemRemoved()
        {
        }

        public ItemRemoved(string orderId, Filling filling)
        {
            OrderId = orderId;
            Filling = filling;
        }

        public string OrderId { get; set; }
        public Filling Filling { get; set; }
    }
}