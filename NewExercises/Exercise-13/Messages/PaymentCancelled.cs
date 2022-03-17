using NServiceBus;

namespace Messages
{
    public class PaymentCancelled : IEvent
    {
        public string CustomerId { get; set; }
        public int Value { get; set; }
    }
}