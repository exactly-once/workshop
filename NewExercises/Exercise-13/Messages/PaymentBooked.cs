using NServiceBus;

namespace Messages
{
    public class PaymentBooked : IEvent
    {
        public string CustomerId { get; set; }
        public int Value { get; set; }
    }
}