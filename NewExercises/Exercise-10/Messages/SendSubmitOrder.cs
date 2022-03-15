namespace Messages
{
    using NServiceBus;

    public class SendSubmitOrder : IMessage
    {
        public string CartId { get; set; }
        public string Customer { get; set; }
    }
}