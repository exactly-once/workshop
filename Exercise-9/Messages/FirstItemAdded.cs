using NServiceBus;

namespace Messages
{
    public class FirstItemAdded : IEvent
    {
        public FirstItemAdded()
        {
        }

        public FirstItemAdded(string orderId)
        {
            OrderId = orderId;
        }

        public string OrderId { get; set; }
    }
}