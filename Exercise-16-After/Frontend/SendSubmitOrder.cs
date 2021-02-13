using NServiceBus;

public class SendSubmitOrder : IMessage
{
    public string OrderId { get; set; }
}
