using NServiceBus.Outbox;

public class OutboxState
{
    public TransportOperation[] OutgoingMessages { get; set; }
}
